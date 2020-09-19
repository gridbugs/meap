use crate::low_level;
use std::env;
use std::error;
use std::fmt;
use std::process;
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
    MultipleMutuallyExclusiveOptionsChosen,
    MissingRequiredArgumentGeneral(String),
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
            Self::MultipleMutuallyExclusiveOptionsChosen => {
                write!(f, "Multiple mutually-exclusive options chosen")
            }
            Self::MissingRequiredArgumentGeneral(error) => write!(f, "{}", error),
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

/// A parser whose one-time-use state has been used up, and is only good for generating help
/// messages.
pub struct SpentParser<P: Parser> {
    parser: P,
    program_name: String,
}

impl<P: Parser> SpentParser<P> {
    pub fn into_help(self) -> Help {
        let mut help = Help::new(self.program_name);
        self.parser.update_help(&mut help);
        help
    }
}

pub trait Parser: Sized {
    type Item;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError>;

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>>;

    fn update_help(&self, help: &mut Help);

    fn parse_args<A: IntoIterator<Item = String>>(
        mut self,
        program_name: String,
        args: A,
    ) -> Result<Self::Item, (Box<dyn error::Error>, SpentParser<Self>)> {
        let mut low_level_parser = low_level::LowLevelParser::new(program_name.clone());
        if let Err(e) = self.register_low_level(&mut low_level_parser) {
            panic!("{}", e);
        }
        let mut low_level_output = match low_level_parser.parse(args) {
            Ok(low_level_output) => low_level_output,
            Err(parse_error) => {
                return Err((
                    parse_error,
                    SpentParser {
                        parser: self,
                        program_name,
                    },
                ))
            }
        };
        let item = match self.parse_low_level(&mut low_level_output) {
            Ok(item) => item,
            Err(parse_error) => {
                return Err((
                    parse_error,
                    SpentParser {
                        parser: self,
                        program_name,
                    },
                ))
            }
        };
        let unhandled_positional_arguments = low_level_output.free_iter().collect::<Vec<_>>();
        if !unhandled_positional_arguments.is_empty() {
            return Err((
                ParseError::UnhandledPositionalArguments(unhandled_positional_arguments).into(),
                SpentParser {
                    parser: self,
                    program_name,
                },
            ));
        }
        Ok(item)
    }

    fn parse_env(self) -> Result<Self::Item, (Box<dyn error::Error>, SpentParser<Self>)> {
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
        Map {
            f: Some(f),
            parser_t: self,
        }
    }

    fn with_help<N: IntoName>(self, name: N) -> WithHelp<Self::Item, Self> {
        WithHelp::new(self, name)
    }

    fn with_help_default(self) -> WithHelp<Self::Item, Self> {
        WithHelp::new_default(self)
    }

    fn with_default_general<T>(self, value: T) -> WithDefaultGeneral<T, Self> {
        WithDefaultGeneral {
            value: Some(value),
            parser: self,
        }
    }

    fn choose_at_most_one<O: Parser>(self, other: O) -> ChooseAtMostOne<Self, O> {
        ChooseAtMostOne(self, other)
    }

    fn with_default_lazy_general<T, F: FnOnce() -> T>(
        self,
        f: F,
    ) -> WithDefaultLazyGeneral<T, F, Self> {
        WithDefaultLazyGeneral {
            value: Some(f),
            parser: self,
        }
    }

    fn required_general<S: AsRef<str>>(self, error_message: S) -> RequiredGeneral<Self> {
        RequiredGeneral {
            parser: self,
            error_message: error_message.as_ref().to_string(),
        }
    }
}

/// Determines how many times the opt can be passed
pub trait Arity {
    fn arity_enum(&self) -> ArityEnum;
}

#[derive(Debug, Clone, Copy)]
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

    #[derive(Debug, Clone)]
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

impl Arg<arity::Optional, has_param::No, name_type::Named> {
    pub fn some_if<T>(self, value: T) -> SomeIf<T> {
        SomeIf {
            value: Some(value),
            arg: self,
        }
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
    fn help_message(&self) -> ArgHelp;
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
    fn help_message(&self) -> ArgHelp {
        ArgHelp::Named(ArgHelpNamed {
            names: self.name_type.clone(),
            hint: self.has_param.maybe_hint().map(|h| h.to_string()),
            description: self.description.clone(),
            arity: self.arity.arity_enum(),
        })
    }
}

impl<V: FromStr, T: From<V>, A: Arity> SingleArgParserHelp
    for Arg<A, has_param::YesVia<V, T>, name_type::Positional>
{
    fn help_message(&self) -> ArgHelp {
        ArgHelp::Positional(ArgHelpPositional {
            hint: self.has_param.hint().to_string(),
            description: self.description.clone(),
            arity: self.arity.arity_enum(),
        })
    }
}

impl<V: FromStr, T: fmt::Display + From<V>>
    Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Named>
{
    pub fn with_default(self, value: T) -> WithDefault<V, T, default_value::Display<T>> {
        WithDefault {
            default_value: default_value::Display::new(value),
            arg: self,
        }
    }
}

impl<V: FromStr, T: From<V>> Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Named> {
    pub fn with_default_lazy<F: FnOnce() -> T, D: AsRef<str>>(
        self,
        description: D,
        thunk: F,
    ) -> WithDefault<V, T, default_value::Lazy<T, F>> {
        WithDefault {
            default_value: default_value::Lazy::new(description.as_ref().to_string(), thunk),
            arg: self,
        }
    }

    pub fn with_default_desc<D: AsRef<str>>(
        self,
        description: D,
        value: T,
    ) -> WithDefault<V, T, default_value::Described<T>> {
        WithDefault {
            default_value: default_value::Described::new(description.as_ref().to_string(), value),
            arg: self,
        }
    }

    pub fn with_default_parse<S: AsRef<str>>(
        self,
        value: S,
    ) -> WithDefault<V, T, default_value::Parsed<V, T>> {
        WithDefault {
            default_value: default_value::Parsed::new(value.as_ref().to_string()),
            arg: self,
        }
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
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        self.parse_single_arg(ll)
    }

    fn update_help(&self, help: &mut Help) {
        match self.help_message() {
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
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        Ok((
            self.parser_t.parse_low_level(ll)?,
            self.parser_u.parse_low_level(ll)?,
        ))
    }

    fn update_help(&self, help: &mut Help) {
        self.parser_t.update_help(help);
        self.parser_u.update_help(help);
    }
}

pub struct Map<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> {
    f: Option<F>,
    parser_t: PT,
}

impl<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> Parser for Map<T, U, F, PT> {
    type Item = U;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.parser_t.register_low_level(ll)
    }

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        Ok((self.f.take().expect("function has already been called"))(
            self.parser_t.parse_low_level(ll)?,
        ))
    }

    fn update_help(&self, help: &mut Help) {
        self.parser_t.update_help(help);
    }
}

impl<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> Map<T, U, F, PT> {
    /// Re-expose `Parser::with_help_default` here so it can be called on the output of the
    /// `let_map!` macro without needing to explicitly use `Parser`.
    pub fn with_help_default(self) -> WithHelp<U, Self> {
        Parser::with_help_default(self)
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
    pub fn new_default(parser_t: PT) -> Self {
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
    pub fn parse_env_or_exit(self) -> T {
        match self.parse_env() {
            Ok(OrHelp::Value(item)) => item,
            Ok(OrHelp::Help(help)) => {
                println!("{}", help);
                process::exit(0);
            }
            Err((error, spent_parser)) => {
                let help = spent_parser.into_help();
                eprintln!("{}\n", error);
                eprintln!("{}", help);
                process::exit(2);
            }
        }
    }
}

impl<T, PT: Parser<Item = T>> Parser for WithHelp<T, PT> {
    type Item = OrHelp<T>;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.parser_t.register_low_level(ll)?;
        ll.register(self.names.names(), low_level::HasParam::No)
    }

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        match ll.get_flag_count(self.names.names()) {
            0 => Ok(OrHelp::Value(self.parser_t.parse_low_level(ll)?)),
            1 => {
                let mut help = Help::new(ll.program_name().to_string());
                self.update_help(&mut help);
                for _ in ll.free_iter() {} // drain the free arguments
                Ok(OrHelp::Help(help))
            }
            _ => Err(ParseError::ExpectedOneArgument(self.names.first_name().clone()).into()),
        }
    }

    fn update_help(&self, help: &mut Help) {
        self.parser_t.update_help(help);
        help.named.push(ArgHelpNamed {
            names: self.names.clone(),
            hint: None,
            description: Some(self.description.clone()),
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

pub trait DefaultValue {
    type Item;
    fn default_value(&mut self) -> Self::Item;
    fn describe(&self) -> String;
}

pub mod default_value {
    use super::DefaultValue;
    use std::fmt;
    use std::marker::PhantomData;
    use std::str::FromStr;

    enum ValueOrDescription<T> {
        Value(T),
        Description(String),
    }

    pub struct Display<T: fmt::Display> {
        value_or_description: ValueOrDescription<T>,
    }

    pub struct Lazy<T, F: FnOnce() -> T> {
        thunk: Option<F>,
        description: String,
    }

    pub struct Described<T> {
        value: Option<T>,
        description: String,
    }

    pub struct Parsed<V: FromStr, T: From<V>> {
        value: String,
        _phantom: PhantomData<(V, T)>,
    }

    impl<T: fmt::Display> Display<T> {
        pub fn new(value: T) -> Self {
            Self {
                value_or_description: ValueOrDescription::Value(value),
            }
        }
    }

    impl<T: fmt::Display> DefaultValue for Display<T> {
        type Item = T;
        fn default_value(&mut self) -> Self::Item {
            use std::mem;
            let value_or_description = mem::replace(
                &mut self.value_or_description,
                ValueOrDescription::Description("".to_string()),
            );
            let value = match value_or_description {
                ValueOrDescription::Value(value) => value,
                ValueOrDescription::Description(_) => panic!("default value has alread been used"),
            };
            self.value_or_description = ValueOrDescription::Description(format!("{}", value));
            value
        }
        fn describe(&self) -> String {
            match &self.value_or_description {
                ValueOrDescription::Description(default_description) => default_description.clone(),
                ValueOrDescription::Value(value) => format!("{}", value),
            }
        }
    }

    impl<T, F: FnOnce() -> T> Lazy<T, F> {
        pub fn new(description: String, thunk: F) -> Self {
            Self {
                thunk: Some(thunk),
                description,
            }
        }
    }

    impl<T, F: FnOnce() -> T> DefaultValue for Lazy<T, F> {
        type Item = T;
        fn default_value(&mut self) -> Self::Item {
            self.thunk.take().expect("function has already been called")()
        }
        fn describe(&self) -> String {
            self.description.clone()
        }
    }

    impl<T> Described<T> {
        pub fn new(description: String, value: T) -> Self {
            Self {
                value: Some(value),
                description,
            }
        }
    }

    impl<T> DefaultValue for Described<T> {
        type Item = T;
        fn default_value(&mut self) -> Self::Item {
            self.value
                .take()
                .expect("default value has already been used")
        }
        fn describe(&self) -> String {
            self.description.clone()
        }
    }

    impl<V: FromStr, T: From<V>> Parsed<V, T> {
        pub fn new(value: String) -> Self {
            Self {
                value,
                _phantom: PhantomData,
            }
        }
    }

    impl<V: FromStr, T: From<V>> DefaultValue for Parsed<V, T> {
        type Item = T;
        fn default_value(&mut self) -> Self::Item {
            if let Ok(t) = self.value.parse::<V>() {
                t.into()
            } else {
                panic!("failed to parse default value: {}", self.value);
            }
        }
        fn describe(&self) -> String {
            self.value.clone()
        }
    }
}

pub struct WithDefault<V: FromStr, T: From<V>, D: DefaultValue<Item = T>> {
    default_value: D,
    arg: Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Named>,
}

impl<V: FromStr, T: From<V>, D: DefaultValue<Item = T>> Parser for WithDefault<V, T, D> {
    type Item = T;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.arg.register_low_level(ll)
    }

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        self.arg
            .parse_low_level(ll)
            .map(|maybe_item| maybe_item.unwrap_or_else(|| self.default_value.default_value()))
    }

    fn update_help(&self, help: &mut Help) {
        let mut help_message = match self.arg.help_message() {
            ArgHelp::Named(help_named) => help_named,
            ArgHelp::Positional(_) => panic!("named arg gave positional help message"),
        };
        help_message.description = Some(if let Some(description) = help_message.description {
            format!(
                "{} (Default: {})",
                description,
                self.default_value.describe()
            )
        } else {
            format!("Default: {}", self.default_value.describe())
        });
        help.named.push(help_message);
    }
}

impl<V: FromStr, T: From<V>, D: DefaultValue<Item = T>> WithDefault<V, T, D> {
    pub fn desc<S: AsRef<str>>(mut self, description: S) -> Self {
        self.arg.description = Some(description.as_ref().to_string());
        self
    }

    pub fn name<N: IntoName>(mut self, name: N) -> Self {
        self.arg.name_type.add(name.into_name());
        self
    }
}

pub struct ChooseAtMostOne<PA: Parser, PB: Parser>(PA, PB);

impl<T, PA: Parser<Item = Option<T>>, PB: Parser<Item = Option<T>>> Parser
    for ChooseAtMostOne<PA, PB>
{
    type Item = Option<T>;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.0.register_low_level(ll)?;
        self.1.register_low_level(ll)
    }

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        let a = self.0.parse_low_level(ll)?;
        let b = self.1.parse_low_level(ll)?;
        match (a, b) {
            (Some(_), Some(_)) => Err(ParseError::MultipleMutuallyExclusiveOptionsChosen.into()),
            (Some(a), None) => Ok(Some(a)),
            (None, Some(b)) => Ok(Some(b)),
            (None, None) => Ok(None),
        }
    }

    fn update_help(&self, help: &mut Help) {
        self.0.update_help(help);
        self.1.update_help(help);
    }
}

pub struct SomeIf<T> {
    value: Option<T>,
    arg: Arg<arity::Optional, has_param::No, name_type::Named>,
}

impl<T> Parser for SomeIf<T> {
    type Item = Option<T>;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.arg.register_low_level(ll)
    }

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        if self.arg.parse_low_level(ll)? {
            Ok(Some(self.value.take().expect("value already used")))
        } else {
            Ok(None)
        }
    }

    fn update_help(&self, help: &mut Help) {
        self.arg.update_help(help);
    }
}

impl<T> SomeIf<T> {
    pub fn desc<S: AsRef<str>>(mut self, description: S) -> Self {
        self.arg.description = Some(description.as_ref().to_string());
        self
    }

    pub fn name<N: IntoName>(mut self, name: N) -> Self {
        self.arg.name_type.add(name.into_name());
        self
    }
}

pub struct WithDefaultGeneral<T, P: Parser> {
    value: Option<T>,
    parser: P,
}

impl<T, P: Parser<Item = Option<T>>> Parser for WithDefaultGeneral<T, P> {
    type Item = T;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.parser.register_low_level(ll)
    }

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        if let Some(value) = self.parser.parse_low_level(ll)? {
            Ok(value)
        } else {
            Ok(self.value.take().expect("value already used"))
        }
    }

    fn update_help(&self, help: &mut Help) {
        self.parser.update_help(help);
    }
}

pub struct WithDefaultLazyGeneral<T, F: FnOnce() -> T, P: Parser> {
    value: Option<F>,
    parser: P,
}

impl<T, F: FnOnce() -> T, P: Parser<Item = Option<T>>> Parser for WithDefaultLazyGeneral<T, F, P> {
    type Item = T;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.parser.register_low_level(ll)
    }

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        if let Some(value) = self.parser.parse_low_level(ll)? {
            Ok(value)
        } else {
            Ok((self.value.take().expect("function already called"))())
        }
    }

    fn update_help(&self, help: &mut Help) {
        self.parser.update_help(help);
    }
}

pub struct RequiredGeneral<P: Parser> {
    parser: P,
    error_message: String,
}

impl<T, P: Parser<Item = Option<T>>> Parser for RequiredGeneral<P> {
    type Item = T;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        self.parser.register_low_level(ll)
    }

    fn parse_low_level(
        &mut self,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        if let Some(value) = self.parser.parse_low_level(ll)? {
            Ok(value)
        } else {
            Err(ParseError::MissingRequiredArgumentGeneral(self.error_message.clone()).into())
        }
    }

    fn update_help(&self, help: &mut Help) {
        self.parser.update_help(help);
    }
}

impl fmt::Display for Help {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        const ARG_SINGLE_LINE_MAX_ARG_LENGTH: usize = 16;
        const OPT_SINGLE_LINE_MAX_ARG_LENGTH: usize = 32;
        const DESCRIPTION_LEFT_PAD: usize = 4;
        write!(f, "Usage: {} [OPTIONS]", self.program_name)?;
        for p in &self.positional {
            match p.arity {
                ArityEnum::Required => write!(f, " {}", p.hint)?,
                ArityEnum::Optional => write!(f, " [{}]", p.hint)?,
                ArityEnum::Multiple => write!(f, " [{} ...]", p.hint)?,
            }
        }
        if !self.positional.is_empty() {
            let parts = self
                .positional
                .iter()
                .map(|p| {
                    let hint = match p.arity {
                        ArityEnum::Required => format!("{}", p.hint),
                        ArityEnum::Optional => format!("[{}]", p.hint),
                        ArityEnum::Multiple => format!("[{} ...]", p.hint),
                    };
                    (hint, p.description.as_ref())
                })
                .collect::<Vec<_>>();
            let max_hint_width = parts
                .iter()
                .filter_map(|p| {
                    if p.0.len() < ARG_SINGLE_LINE_MAX_ARG_LENGTH {
                        Some(p.0.len())
                    } else {
                        None
                    }
                })
                .max()
                .unwrap_or(0)
                + DESCRIPTION_LEFT_PAD;
            write!(f, "\n\nArgs:")?;
            for (hint, description) in parts {
                writeln!(f)?;
                if let Some(description) = description {
                    if hint.len() < ARG_SINGLE_LINE_MAX_ARG_LENGTH {
                        write!(
                            f,
                            "    {:width$} {}",
                            hint,
                            description,
                            width = max_hint_width,
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
            let parts = self
                .named
                .iter()
                .map(|n| {
                    let name_list = n
                        .names
                        .names()
                        .iter()
                        .map(|name| name.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    let name_list_with_arity = match (n.arity, n.hint.as_ref()) {
                        (ArityEnum::Required, None) => format!("{}", name_list),
                        (ArityEnum::Optional, None) => format!("[{}]", name_list),
                        (ArityEnum::Multiple, None) => format!("[{} ...]", name_list),
                        (ArityEnum::Required, Some(hint)) => format!("{} {}", name_list, hint),
                        (ArityEnum::Optional, Some(hint)) => format!("[{} {}]", name_list, hint),
                        (ArityEnum::Multiple, Some(hint)) => {
                            format!("[{} {} ...]", name_list, hint)
                        }
                    };
                    (name_list_with_arity, n.description.as_ref())
                })
                .collect::<Vec<_>>();
            let max_name_list_width = parts
                .iter()
                .filter_map(|p| {
                    if p.0.len() < OPT_SINGLE_LINE_MAX_ARG_LENGTH {
                        Some(p.0.len())
                    } else {
                        None
                    }
                })
                .max()
                .unwrap_or(0)
                + DESCRIPTION_LEFT_PAD;
            write!(f, "\n\nOptions:")?;
            for (name_list, description) in parts {
                writeln!(f)?;
                if let Some(description) = description {
                    if name_list.len() < OPT_SINGLE_LINE_MAX_ARG_LENGTH {
                        write!(
                            f,
                            "    {:width$} {}",
                            name_list,
                            description,
                            width = max_name_list_width,
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
