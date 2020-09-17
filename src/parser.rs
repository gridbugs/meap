use crate::low_level;
use std::env;
use std::error;
use std::fmt;
use std::str::FromStr;

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Name {
    Long(String),
    Short(char),
}

impl Name {
    fn to_string(&self) -> String {
        format!("{}", self)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Long(long) => write!(f, "--{}", long),
            Self::Short(short) => write!(f, "-{}", short),
        }
    }
}

pub trait IntoName {
    fn into_name(self) -> Name;
}

impl IntoName for Name {
    fn into_name(self) -> Name {
        self
    }
}

impl IntoName for char {
    fn into_name(self) -> Name {
        Name::Short(self)
    }
}

impl<'a> IntoName for &'a str {
    fn into_name(self) -> Name {
        Name::Long(self.to_string())
    }
}

impl IntoName for String {
    fn into_name(self) -> Name {
        Name::Long(self)
    }
}

#[derive(Debug)]
pub enum ParseError {
    UnhandledPositionalArguments(Vec<String>),
    UnknownName(Name),
    ArgumentLacksParameter(Name),
    UnexpectedArgumentParam { name: Name, value: String },
    MissingRequiredPositionalArgument(String),
    MissingRequiredArgument(Name),
    ExpectedOneArgument(Name),
    UnableToParsePositionalArgumentParam { hint: String, value: String },
    UnableToParseArgumentParam { name: Name, value: String },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::UnhandledPositionalArguments(values) => {
                write!(f, "Unhandled positional arguments: {}", values.join(", "))
            }
            Self::UnknownName(name) => write!(f, "Argument \"{}\" does not exist", name),
            Self::ArgumentLacksParameter(name) => {
                write!(f, "Argument \"{}\" lacks parameter", name)
            }
            Self::UnexpectedArgumentParam { name, value } => {
                write!(f, "Unexpected param \"{}\" to argument \"{}\"", value, name)
            }
            Self::MissingRequiredPositionalArgument(hint) => {
                write!(f, "Required positional argument \"{}\" is missing", hint)
            }
            Self::MissingRequiredArgument(name) => {
                write!(f, "Required argument \"{}\" is missing", name)
            }
            Self::ExpectedOneArgument(name) => write!(
                f,
                "Argument \"{}\" was passed multiple times but expected at most once",
                name
            ),
            Self::UnableToParsePositionalArgumentParam { hint, value } => write!(
                f,
                "Unable to parse \"{}\" given for positional argument \"{}\"",
                value, hint
            ),
            Self::UnableToParseArgumentParam { name, value } => write!(
                f,
                "Unable to parse value \"{}\" given for argument \"{}\"",
                value, name
            ),
        }
    }
}

impl error::Error for ParseError {}

#[derive(Debug)]
pub enum SpecError {
    NameUsedMultipleTimes(Name),
}

impl fmt::Display for SpecError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::NameUsedMultipleTimes(name) => {
                write!(f, "Name used multiple times: {}", name.to_string())
            }
        }
    }
}

impl error::Error for SpecError {}

pub trait Parser: Sized {
    type Item;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError>;

    fn parse_low_level(
        self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>>;

    fn allow_unhandled_args(&self) -> bool {
        false
    }

    fn update_help(self, help: &mut Help);

    fn parse_args<A: IntoIterator<Item = String>>(
        self,
        program_name: String,
        args: A,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        let mut low_level_parser = low_level::LowLevelParser::new(program_name);
        if let Err(e) = self.register_low_level(&mut low_level_parser) {
            panic!("{}", e);
        }
        let mut low_level_output = low_level_parser.parse(args)?;
        let allow_unhandled_args = self.allow_unhandled_args();
        let item = self.parse_low_level(&mut low_level_output)?;
        let unhandled_positional_arguments = low_level_output.free_iter().collect::<Vec<_>>();
        if !allow_unhandled_args && !unhandled_positional_arguments.is_empty() {
            return Err(
                ParseError::UnhandledPositionalArguments(unhandled_positional_arguments).into(),
            );
        }
        Ok(item)
    }

    fn parse_env(self) -> Result<Self::Item, Box<dyn error::Error>> {
        let mut env = env::args();
        let program_name = env.next().expect("no args");
        self.parse_args(program_name, env)
    }

    fn both<PU: Parser>(self, other: PU) -> Both<Self::Item, PU::Item, Self, PU> {
        Both {
            parser_t: self,
            parser_u: other,
        }
    }

    fn map<U, F: FnOnce(Self::Item) -> U>(self, f: F) -> Map<Self::Item, U, F, Self> {
        Map { f, parser_t: self }
    }

    fn with_help<N: IntoName>(self, name: N) -> WithHelp<Self::Item, Self> {
        WithHelp::new(self, name)
    }

    fn with_help_default_names(self) -> WithHelp<Self::Item, Self> {
        WithHelp::new_default_names(self)
    }
}

/// Determines how many times the opt can be passed
pub trait Arity {
    fn arity_enum(&self) -> ArityEnum;
}

#[derive(Debug)]
pub enum ArityEnum {
    Required,
    Optional,
    Multiple,
}

pub mod arity {
    use super::{Arity, ArityEnum};

    pub struct Required;
    pub struct Optional;
    pub struct Multiple;

    impl Arity for Required {
        fn arity_enum(&self) -> ArityEnum {
            ArityEnum::Required
        }
    }
    impl Arity for Optional {
        fn arity_enum(&self) -> ArityEnum {
            ArityEnum::Optional
        }
    }
    impl Arity for Multiple {
        fn arity_enum(&self) -> ArityEnum {
            ArityEnum::Multiple
        }
    }
}

/// Determines whether the opt takes a value as an argument
pub trait HasParam {
    fn low_level() -> low_level::HasParam;
    fn maybe_hint(&self) -> Option<&str>;
}

pub mod has_param {
    use super::{low_level, HasParam};
    use std::marker::PhantomData;
    use std::str::FromStr;

    pub struct YesVia<V: FromStr, T: From<V>> {
        hint: String,
        phantom: PhantomData<(V, T)>,
    }
    pub struct No;

    impl<V: FromStr, T: From<V>> HasParam for YesVia<V, T> {
        fn low_level() -> low_level::HasParam {
            low_level::HasParam::Yes
        }
        fn maybe_hint(&self) -> Option<&str> {
            Some(self.hint.as_str())
        }
    }
    impl HasParam for No {
        fn low_level() -> low_level::HasParam {
            low_level::HasParam::No
        }
        fn maybe_hint(&self) -> Option<&str> {
            None
        }
    }

    impl<V: FromStr, T: From<V>> YesVia<V, T> {
        pub fn new<H: AsRef<str>>(hint: H) -> Self {
            Self {
                hint: hint.as_ref().to_string(),
                phantom: PhantomData,
            }
        }
        pub fn hint(&self) -> &str {
            self.hint.as_str()
        }
    }
}

pub trait NameType {
    fn names_to_register(&self) -> Option<&[Name]>;
}

pub mod name_type {
    use super::{IntoName, Name, NameType};

    #[derive(Debug)]
    pub struct Named {
        names: Vec<Name>,
    }
    pub struct Positional;

    impl NameType for Named {
        fn names_to_register(&self) -> Option<&[Name]> {
            Some(&self.names)
        }
    }
    impl NameType for Positional {
        fn names_to_register(&self) -> Option<&[Name]> {
            None
        }
    }

    impl Named {
        pub fn new<N: IntoName>(name: N) -> Self {
            Self {
                names: vec![name.into_name()],
            }
        }
        pub fn add<N: IntoName>(&mut self, name: N) {
            self.names.push(name.into_name());
        }
        pub fn names(&self) -> &[Name] {
            &self.names
        }
        pub fn first_name(&self) -> &Name {
            &self.names[0]
        }
    }
}

pub struct Arg<A: Arity, H: HasParam, N: NameType> {
    description: Option<String>,
    name_type: N,
    has_param: H,
    arity: A,
}

impl<A: Arity, H: HasParam, N: NameType> Arg<A, H, N> {
    pub fn new(arity: A, has_param: H, name_type: N) -> Self {
        Arg {
            description: None,
            name_type,
            has_param,
            arity,
        }
    }

    pub fn desc<S: AsRef<str>>(mut self, description: S) -> Self {
        self.description = Some(description.as_ref().to_string());
        self
    }
}

impl<A: Arity, H: HasParam> Arg<A, H, name_type::Named> {
    pub fn name<N: IntoName>(mut self, name: N) -> Self {
        self.name_type.add(name.into_name());
        self
    }
}

pub trait SingleArgParser {
    type SingleArgItem;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>>;
}

pub trait SingleArgParserHelp {
    fn into_help_message(self) -> ArgHelp;
}

impl<V: FromStr, T: From<V>> SingleArgParser
    for Arg<arity::Required, has_param::YesVia<V, T>, name_type::Positional>
{
    type SingleArgItem = T;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let value = ll.free_iter().next().ok_or_else(|| {
            ParseError::MissingRequiredPositionalArgument(self.has_param.hint().to_string())
        })?;
        Ok(T::from(value.parse().map_err(|_| {
            ParseError::UnableToParsePositionalArgumentParam {
                hint: self.has_param.hint().to_string(),
                value,
            }
        })?))
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser
    for Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Positional>
{
    type SingleArgItem = Option<T>;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        if let Some(value) = ll.free_iter().next() {
            Ok(Some(T::from(value.parse().map_err(|_| {
                ParseError::UnableToParsePositionalArgumentParam {
                    hint: self.has_param.hint().to_string(),
                    value,
                }
            })?)))
        } else {
            Ok(None)
        }
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser
    for Arg<arity::Multiple, has_param::YesVia<V, T>, name_type::Positional>
{
    type SingleArgItem = Vec<T>;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let mut ret = Vec::new();
        for value in ll.free_iter() {
            ret.push(T::from(value.parse().map_err(|_| {
                ParseError::UnableToParsePositionalArgumentParam {
                    hint: self.has_param.hint().to_string(),
                    value,
                }
            })?));
        }
        Ok(ret)
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser
    for Arg<arity::Required, has_param::YesVia<V, T>, name_type::Named>
{
    type SingleArgItem = T;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let values = ll.get_opt_values(self.name_type.names());
        match values.len() {
            0 => {
                Err(ParseError::MissingRequiredArgument(self.name_type.first_name().clone()).into())
            }
            1 => Ok(T::from(values[0].parse().map_err(|_| {
                ParseError::UnableToParseArgumentParam {
                    name: self.name_type.first_name().clone(),
                    value: values[0].clone(),
                }
            })?)),
            _ => Err(ParseError::ExpectedOneArgument(self.name_type.first_name().clone()).into()),
        }
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser
    for Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Named>
{
    type SingleArgItem = Option<T>;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let values = ll.get_opt_values(self.name_type.names());
        match values.len() {
            0 => Ok(None),
            1 => Ok(Some(T::from(values[0].parse().map_err(|_| {
                ParseError::UnableToParseArgumentParam {
                    name: self.name_type.first_name().clone(),
                    value: values[0].clone(),
                }
            })?))),
            _ => Err(ParseError::ExpectedOneArgument(self.name_type.first_name().clone()).into()),
        }
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser
    for Arg<arity::Multiple, has_param::YesVia<V, T>, name_type::Named>
{
    type SingleArgItem = Vec<T>;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let values = ll.get_opt_values(self.name_type.names());
        let mut ret = Vec::with_capacity(values.len());
        for v in values {
            ret.push(T::from(v.parse().map_err(|_| {
                ParseError::UnableToParseArgumentParam {
                    name: self.name_type.first_name().clone(),
                    value: v.clone(),
                }
            })?));
        }
        Ok(ret)
    }
}

impl SingleArgParser for Arg<arity::Optional, has_param::No, name_type::Named> {
    type SingleArgItem = bool;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        match ll.get_flag_count(self.name_type.names()) {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(ParseError::ExpectedOneArgument(self.name_type.first_name().clone()).into()),
        }
    }
}

impl SingleArgParser for Arg<arity::Multiple, has_param::No, name_type::Named> {
    type SingleArgItem = usize;

    fn parse_single_arg(
        &self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        Ok(ll.get_flag_count(self.name_type.names()))
    }
}

impl<A: Arity, H: HasParam> SingleArgParserHelp for Arg<A, H, name_type::Named> {
    fn into_help_message(self) -> ArgHelp {
        ArgHelp::Named(ArgHelpNamed {
            names: self.name_type,
            hint: self.has_param.maybe_hint().map(|h| h.to_string()),
            description: self.description,
            arity: self.arity.arity_enum(),
        })
    }
}

impl<V: FromStr, T: From<V>, A: Arity> SingleArgParserHelp
    for Arg<A, has_param::YesVia<V, T>, name_type::Positional>
{
    fn into_help_message(self) -> ArgHelp {
        ArgHelp::Positional(ArgHelpPositional {
            hint: self.has_param.hint().to_string(),
            description: self.description,
            arity: self.arity.arity_enum(),
        })
    }
}

impl<A: Arity, H: HasParam, N: NameType> Parser for Arg<A, H, N>
where
    Self: SingleArgParser + SingleArgParserHelp,
{
    type Item = <Self as SingleArgParser>::SingleArgItem;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        if let Some(names) = self.name_type.names_to_register() {
            ll.register(names, H::low_level())?;
        }
        Ok(())
    }

    fn parse_low_level(
        self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        self.parse_single_arg(ll)
    }

    fn update_help(self, help: &mut Help) {
        match self.into_help_message() {
            ArgHelp::Named(help_named) => help.named.push(help_named),
            ArgHelp::Positional(help_positional) => help.positional.push(help_positional),
        }
    }
}

pub struct Both<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> {
    parser_t: PT,
    parser_u: PU,
}

impl<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> Parser for Both<T, U, PT, PU> {
    type Item = (T, U);

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.parser_t.register_low_level(ll)?;
        self.parser_u.register_low_level(ll)
    }

    fn parse_low_level(
        self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        Ok((
            self.parser_t.parse_low_level(ll)?,
            self.parser_u.parse_low_level(ll)?,
        ))
    }

    fn update_help(self, help: &mut Help) {
        self.parser_t.update_help(help);
        self.parser_u.update_help(help);
    }
}

impl<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> Both<T, U, PT, PU> {
    pub fn parse_env(self) -> Result<(T, U), Box<dyn error::Error>> {
        <Self as Parser>::parse_env(self)
    }

    pub fn with_help<N: IntoName>(self, name: N) -> WithHelp<(T, U), Self> {
        WithHelp::new(self, name)
    }

    pub fn with_help_default_names(self) -> WithHelp<(T, U), Self> {
        WithHelp::new_default_names(self)
    }
}

pub struct Map<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> {
    f: F,
    parser_t: PT,
}

impl<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> Parser for Map<T, U, F, PT> {
    type Item = U;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.parser_t.register_low_level(ll)
    }

    fn parse_low_level(
        self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        Ok((self.f)(self.parser_t.parse_low_level(ll)?))
    }

    fn update_help(self, help: &mut Help) {
        self.parser_t.update_help(help);
    }
}

impl<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> Map<T, U, F, PT> {
    pub fn parse_env(self) -> Result<U, Box<dyn error::Error>> {
        <Self as Parser>::parse_env(self)
    }

    pub fn with_help<N: IntoName>(self, name: N) -> WithHelp<U, Self> {
        WithHelp::new(self, name)
    }

    pub fn with_help_default_names(self) -> WithHelp<U, Self> {
        WithHelp::new_default_names(self)
    }
}

#[derive(Debug)]
pub enum OrHelp<T> {
    Value(T),
    Help(Help),
}

pub struct WithHelp<T, PT: Parser<Item = T>> {
    parser_t: PT,
    names: name_type::Named,
    description: String,
}

impl<T, PT: Parser<Item = T>> WithHelp<T, PT> {
    pub fn new<N: IntoName>(parser_t: PT, name: N) -> Self {
        Self {
            parser_t,
            names: name_type::Named::new(name),
            description: "print help message".to_string(),
        }
    }
    pub fn new_default_names(parser_t: PT) -> Self {
        Self::new(parser_t, 'h').name("help")
    }
    pub fn desc<S: AsRef<str>>(mut self, description: S) -> Self {
        self.description = description.as_ref().to_string();
        self
    }
    pub fn name<N: IntoName>(mut self, name: N) -> Self {
        self.names.add(name.into_name());
        self
    }
    pub fn parse_env(self) -> Result<OrHelp<T>, Box<dyn error::Error>> {
        <Self as Parser>::parse_env(self)
    }
}

impl<T, PT: Parser<Item = T>> Parser for WithHelp<T, PT> {
    type Item = OrHelp<T>;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.parser_t.register_low_level(ll)?;
        ll.register(self.names.names(), low_level::HasParam::No)
    }

    fn parse_low_level(
        self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        match ll.get_flag_count(self.names.names()) {
            0 => Ok(OrHelp::Value(self.parser_t.parse_low_level(ll)?)),
            1 => {
                let mut help = Help::new(ll.program_name().to_string());
                self.update_help(&mut help);
                Ok(OrHelp::Help(help))
            }
            _ => Err(ParseError::ExpectedOneArgument(self.names.first_name().clone()).into()),
        }
    }

    fn allow_unhandled_args(&self) -> bool {
        true
    }

    fn update_help(self, help: &mut Help) {
        self.parser_t.update_help(help);
        help.named.push(ArgHelpNamed {
            names: self.names,
            hint: None,
            description: Some(self.description),
            arity: ArityEnum::Optional,
        });
    }
}

#[derive(Debug)]
pub struct ArgHelpPositional {
    pub hint: String,
    pub description: Option<String>,
    pub arity: ArityEnum,
}

#[derive(Debug)]
pub struct ArgHelpNamed {
    pub names: name_type::Named,
    pub hint: Option<String>,
    pub description: Option<String>,
    pub arity: ArityEnum,
}

#[derive(Debug)]
pub enum ArgHelp {
    Positional(ArgHelpPositional),
    Named(ArgHelpNamed),
}

#[derive(Debug)]
pub struct Help {
    pub program_name: String,
    pub positional: Vec<ArgHelpPositional>,
    pub named: Vec<ArgHelpNamed>,
}

impl Help {
    pub fn new(program_name: String) -> Self {
        Self {
            program_name,
            positional: Vec::new(),
            named: Vec::new(),
        }
    }
}

impl fmt::Display for Help {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        const ARG_SINGLE_LINE_MAX_ARG_LENGTH: usize = 16;
        const OPT_SINGLE_LINE_MAX_ARG_LENGTH: usize = 32;
        write!(f, "Usage: {} [OPTIONS]", self.program_name)?;
        for p in &self.positional {
            match p.arity {
                ArityEnum::Required => write!(f, " {}", p.hint)?,
                ArityEnum::Optional => write!(f, " [{}]", p.hint)?,
                ArityEnum::Multiple => write!(f, " [{} ...]", p.hint)?,
            }
        }
        if !self.positional.is_empty() {
            write!(f, "\n\nArgs:")?;
            for p in &self.positional {
                writeln!(f)?;
                let hint = match p.arity {
                    ArityEnum::Required => format!("{}", p.hint),
                    ArityEnum::Optional => format!("[{}]", p.hint),
                    ArityEnum::Multiple => format!("[{} ...]", p.hint),
                };
                if let Some(description) = p.description.as_ref() {
                    if hint.len() < ARG_SINGLE_LINE_MAX_ARG_LENGTH {
                        write!(
                            f,
                            "    {:width$} {}",
                            hint,
                            description,
                            width = ARG_SINGLE_LINE_MAX_ARG_LENGTH,
                        )?;
                    } else {
                        writeln!(f, "    {}", hint)?;
                        write!(f, "                {}", description)?;
                    }
                } else {
                    write!(f, "    {}", hint)?;
                }
            }
        }
        if !self.named.is_empty() {
            write!(f, "\n\nOptions:")?;
            for n in &self.named {
                writeln!(f)?;
                let name_list = n
                    .names
                    .names()
                    .iter()
                    .map(|name| name.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                if let Some(description) = n.description.as_ref() {
                    if name_list.len() < OPT_SINGLE_LINE_MAX_ARG_LENGTH {
                        write!(
                            f,
                            "    {:width$} {}",
                            name_list,
                            description,
                            width = OPT_SINGLE_LINE_MAX_ARG_LENGTH,
                        )?;
                    } else {
                        writeln!(f, "    {}", name_list)?;
                        write!(f, "                {}", description)?;
                    }
                } else {
                    write!(f, "    {}", name_list)?;
                }
            }
        }
        Ok(())
    }
}
