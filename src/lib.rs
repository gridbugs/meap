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
    UnableToParsePositionalArgumentParam { name: String, value: String },
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
            Self::MissingRequiredPositionalArgument(name) => {
                write!(f, "Required positional argument \"{}\" is missing", name)
            }
            Self::MissingRequiredArgument(name) => {
                write!(f, "Required argument \"{}\" is missing", name)
            }
            Self::ExpectedOneArgument(name) => write!(
                f,
                "Argument \"{}\" was passed multiple times but expected at most once",
                name
            ),
            Self::UnableToParseArgumentParam { name, value } => write!(
                f,
                "Unable to parse value \"{}\" given for argument \"{}\"",
                value, name
            ),
            Self::UnableToParsePositionalArgumentParam { name, value } => write!(
                f,
                "Unable to parse \"{}\" given for positional argument \"{}\"",
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

    fn parse_args<A: IntoIterator<Item = String>>(
        self,
        args: A,
    ) -> Result<Self::Item, Box<dyn error::Error>> {
        let mut low_level_parser = low_level::LowLevelParser::default();
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
        self.parse_args(env::args().skip(1))
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
pub trait Arity {}

pub mod arity {
    use super::Arity;

    pub struct Required;
    pub struct Optional;
    pub struct Multiple;

    impl Arity for Required {}
    impl Arity for Optional {}
    impl Arity for Multiple {}
}

/// Determines whether the opt takes a value as an argument
pub trait HasParam {
    fn low_level() -> low_level::HasParam;
}

pub mod has_param {
    use super::{low_level, HasParam};
    use std::marker::PhantomData;
    use std::str::FromStr;

    pub struct YesVia<V: FromStr, T: From<V>>(PhantomData<(V, T)>);
    pub struct No;

    impl<V: FromStr, T: From<V>> HasParam for YesVia<V, T> {
        fn low_level() -> low_level::HasParam {
            low_level::HasParam::Yes
        }
    }
    impl HasParam for No {
        fn low_level() -> low_level::HasParam {
            low_level::HasParam::No
        }
    }

    impl<V: FromStr, T: From<V>> Default for YesVia<V, T> {
        fn default() -> Self {
            Self(PhantomData)
        }
    }
}

pub trait NameType {
    fn names_to_register(&self) -> Option<&[Name]>;
}

pub mod name_type {
    use super::{IntoName, Name, NameType};

    pub struct Named {
        names: Vec<Name>,
    }
    pub struct Positional {
        name: String,
    }

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

    impl Positional {
        pub fn new<N: AsRef<str>>(name: N) -> Self {
            Self {
                name: name.as_ref().to_string(),
            }
        }
        pub fn name(&self) -> &str {
            self.name.as_str()
        }
    }
}

pub struct Arg<A: Arity, H: HasParam, N: NameType> {
    description: Option<String>,
    hint: Option<String>,
    name_type: N,
    _arity: A,
    _has_param: H,
}

impl<A: Arity, H: HasParam, N: NameType> Arg<A, H, N> {
    pub fn description<S: AsRef<str>>(mut self, description: S) -> Self {
        self.description = Some(description.as_ref().to_string());
        self
    }
    pub fn d<S: AsRef<str>>(self, description: S) -> Self {
        self.description(description)
    }
}

impl<A: Arity, H: HasParam> Arg<A, H, name_type::Named> {
    pub fn name<N: IntoName>(mut self, name: N) -> Self {
        self.name_type.add(name.into_name());
        self
    }
    pub fn long<S: AsRef<str>>(self, long: S) -> Self {
        self.name(long.as_ref())
    }
    pub fn short(self, short: char) -> Self {
        self.name(short)
    }
    pub fn n<N: IntoName>(self, name: N) -> Self {
        self.name(name)
    }
    pub fn l<S: AsRef<str>>(self, long: S) -> Self {
        self.long(long)
    }
    pub fn s(self, short: char) -> Self {
        self.short(short)
    }
}

impl<V: FromStr, T: From<V>, A: Arity> Arg<A, has_param::YesVia<V, T>, name_type::Named> {
    pub fn hint<S: AsRef<str>>(mut self, hint: S) -> Self {
        self.hint = Some(hint.as_ref().to_string());
        self
    }
    pub fn h<S: AsRef<str>>(self, hint: S) -> Self {
        self.hint(hint)
    }
}

pub trait SingleArgParser<N: NameType> {
    type SingleArgItem;

    fn parse_single_arg(
        &self,
        name_type: &N,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>>;
}

impl<V: FromStr, T: From<V>> SingleArgParser<name_type::Positional>
    for Arg<arity::Required, has_param::YesVia<V, T>, name_type::Positional>
{
    type SingleArgItem = T;

    fn parse_single_arg(
        &self,
        name_type: &name_type::Positional,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let value = ll.free_iter().next().ok_or_else(|| {
            ParseError::MissingRequiredPositionalArgument(name_type.name().to_string())
        })?;
        Ok(T::from(value.parse().map_err(|_| {
            ParseError::UnableToParsePositionalArgumentParam {
                name: name_type.name().to_string(),
                value,
            }
        })?))
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser<name_type::Positional>
    for Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Positional>
{
    type SingleArgItem = Option<T>;

    fn parse_single_arg(
        &self,
        name_type: &name_type::Positional,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        if let Some(value) = ll.free_iter().next() {
            Ok(Some(T::from(value.parse().map_err(|_| {
                ParseError::UnableToParsePositionalArgumentParam {
                    name: name_type.name().to_string(),
                    value,
                }
            })?)))
        } else {
            Ok(None)
        }
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser<name_type::Positional>
    for Arg<arity::Multiple, has_param::YesVia<V, T>, name_type::Positional>
{
    type SingleArgItem = Vec<T>;

    fn parse_single_arg(
        &self,
        name_type: &name_type::Positional,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let mut ret = Vec::new();
        for value in ll.free_iter() {
            ret.push(T::from(value.parse().map_err(|_| {
                ParseError::UnableToParsePositionalArgumentParam {
                    name: name_type.name().to_string(),
                    value,
                }
            })?));
        }
        Ok(ret)
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser<name_type::Named>
    for Arg<arity::Required, has_param::YesVia<V, T>, name_type::Named>
{
    type SingleArgItem = T;

    fn parse_single_arg(
        &self,
        name_type: &name_type::Named,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let values = ll.get_opt_values(name_type.names());
        match values.len() {
            0 => Err(ParseError::MissingRequiredArgument(name_type.first_name().clone()).into()),
            1 => Ok(T::from(values[0].parse().map_err(|_| {
                ParseError::UnableToParseArgumentParam {
                    name: name_type.first_name().clone(),
                    value: values[0].clone(),
                }
            })?)),
            _ => Err(ParseError::ExpectedOneArgument(name_type.first_name().clone()).into()),
        }
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser<name_type::Named>
    for Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Named>
{
    type SingleArgItem = Option<T>;

    fn parse_single_arg(
        &self,
        name_type: &name_type::Named,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let values = ll.get_opt_values(name_type.names());
        match values.len() {
            0 => Ok(None),
            1 => Ok(Some(T::from(values[0].parse().map_err(|_| {
                ParseError::UnableToParseArgumentParam {
                    name: name_type.first_name().clone(),
                    value: values[0].clone(),
                }
            })?))),
            _ => Err(ParseError::ExpectedOneArgument(name_type.first_name().clone()).into()),
        }
    }
}

impl<V: FromStr, T: From<V>> SingleArgParser<name_type::Named>
    for Arg<arity::Multiple, has_param::YesVia<V, T>, name_type::Named>
{
    type SingleArgItem = Vec<T>;

    fn parse_single_arg(
        &self,
        name_type: &name_type::Named,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        let values = ll.get_opt_values(name_type.names());
        let mut ret = Vec::with_capacity(values.len());
        for v in values {
            ret.push(T::from(v.parse().map_err(|_| {
                ParseError::UnableToParseArgumentParam {
                    name: name_type.first_name().clone(),
                    value: v.clone(),
                }
            })?));
        }
        Ok(ret)
    }
}

impl SingleArgParser<name_type::Named> for Arg<arity::Optional, has_param::No, name_type::Named> {
    type SingleArgItem = bool;

    fn parse_single_arg(
        &self,
        name_type: &name_type::Named,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        match ll.get_flag_count(name_type.names()) {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(ParseError::ExpectedOneArgument(name_type.first_name().clone()).into()),
        }
    }
}

impl SingleArgParser<name_type::Named> for Arg<arity::Multiple, has_param::No, name_type::Named> {
    type SingleArgItem = usize;

    fn parse_single_arg(
        &self,
        name_type: &name_type::Named,
        ll: &mut low_level::LowLevelParserOutput,
    ) -> Result<Self::SingleArgItem, Box<dyn error::Error>> {
        Ok(ll.get_flag_count(name_type.names()))
    }
}

impl<A: Arity, H: HasParam, N: NameType> Parser for Arg<A, H, N>
where
    Self: SingleArgParser<N>,
{
    type Item = <Self as SingleArgParser<N>>::SingleArgItem;

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
        self.parse_single_arg(&self.name_type, ll)
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
    Help,
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
        Self::new(parser_t, 'h').long("help")
    }
    pub fn description<S: AsRef<str>>(mut self, description: S) -> Self {
        self.description = description.as_ref().to_string();
        self
    }
    pub fn d<S: AsRef<str>>(self, description: S) -> Self {
        self.description(description)
    }
    pub fn name<N: IntoName>(mut self, name: N) -> Self {
        self.names.add(name.into_name());
        self
    }
    pub fn long<S: AsRef<str>>(self, long: S) -> Self {
        self.name(long.as_ref())
    }
    pub fn short(self, short: char) -> Self {
        self.name(short)
    }
    pub fn n<N: IntoName>(self, name: N) -> Self {
        self.name(name)
    }
    pub fn l<S: AsRef<str>>(self, long: S) -> Self {
        self.long(long)
    }
    pub fn s(self, short: char) -> Self {
        self.short(short)
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
            1 => Ok(OrHelp::Help),
            _ => Err(ParseError::ExpectedOneArgument(self.names.first_name().clone()).into()),
        }
    }

    fn allow_unhandled_args(&self) -> bool {
        true
    }
}

#[macro_export]
macro_rules! unflatten_closure {
    ( $p:pat => $tup:expr ) => {
        |$p| $tup
    };
    ( $p:pat => ( $($tup:tt)* ), $head:expr $(, $tail:expr)* ) => {
        $crate::unflatten_closure!( ($p, a) => ( $($tup)*, a) $(, $tail )* )
    };
}

#[macro_export]
macro_rules! args_all {
    ( $only:expr ) => {
        $only
    };
    ( $head:expr, $($tail:expr),* $(,)* ) => {
        $head $( .both($tail) )*
            .map(
                $crate::unflatten_closure!(a => (a) $(, $tail )*)
            )
    };
}

#[macro_export]
macro_rules! args_map {
    ( let { $var1:ident = $a1:expr; } in { $b:expr } ) => {
        {
            use $crate::prelude::*;
            $a1.map(|$var1| $b)
        }
    };
    ( let { $var1:ident = $a1:expr; $($var:ident = $a:expr;)+ } in { $b:expr } ) => {
        {
            use $crate::prelude::*;
            { $crate::args_all! {
                                    $a1, $($a),*
                                } } .map(|($var1, $($var),*)| $b)
        }
    };
}

pub mod prelude {
    pub use super::Parser;
    use super::*;

    pub fn arg<A: Arity, H: HasParam, N: NameType>(
        arity: A,
        has_param: H,
        name_type: N,
    ) -> Arg<A, H, N> {
        Arg {
            description: None,
            hint: None,
            name_type,
            _arity: arity,
            _has_param: has_param,
        }
    }

    pub fn pos_opt<T: FromStr>(
        name: &str,
    ) -> Arg<arity::Optional, has_param::YesVia<T, T>, name_type::Positional> {
        arg(
            arity::Optional,
            has_param::YesVia::default(),
            name_type::Positional::new(name),
        )
    }

    pub fn pos_req<T: FromStr>(
        name: &str,
    ) -> Arg<arity::Required, has_param::YesVia<T, T>, name_type::Positional> {
        arg(
            arity::Required,
            has_param::YesVia::default(),
            name_type::Positional::new(name),
        )
    }

    pub fn pos_multi<T: FromStr>(
        name: &str,
    ) -> Arg<arity::Multiple, has_param::YesVia<T, T>, name_type::Positional> {
        arg(
            arity::Multiple,
            has_param::YesVia::default(),
            name_type::Positional::new(name),
        )
    }

    pub fn pos_opt_via<V: FromStr, T: From<V>>(
        name: &str,
    ) -> Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Positional> {
        arg(
            arity::Optional,
            has_param::YesVia::default(),
            name_type::Positional::new(name),
        )
    }

    pub fn pos_req_via<V: FromStr, T: From<V>>(
        name: &str,
    ) -> Arg<arity::Required, has_param::YesVia<V, T>, name_type::Positional> {
        arg(
            arity::Required,
            has_param::YesVia::default(),
            name_type::Positional::new(name),
        )
    }

    pub fn pos_multi_via<V: FromStr, T: From<V>>(
        name: &str,
    ) -> Arg<arity::Multiple, has_param::YesVia<V, T>, name_type::Positional> {
        arg(
            arity::Multiple,
            has_param::YesVia::default(),
            name_type::Positional::new(name),
        )
    }

    pub fn opt_opt<T: FromStr, N: IntoName>(
        name: N,
    ) -> Arg<arity::Optional, has_param::YesVia<T, T>, name_type::Named> {
        arg(
            arity::Optional,
            has_param::YesVia::default(),
            name_type::Named::new(name),
        )
    }

    pub fn opt_req<T: FromStr, N: IntoName>(
        name: N,
    ) -> Arg<arity::Required, has_param::YesVia<T, T>, name_type::Named> {
        arg(
            arity::Required,
            has_param::YesVia::default(),
            name_type::Named::new(name),
        )
    }

    pub fn opt_multi<T: FromStr, N: IntoName>(
        name: N,
    ) -> Arg<arity::Multiple, has_param::YesVia<T, T>, name_type::Named> {
        arg(
            arity::Multiple,
            has_param::YesVia::default(),
            name_type::Named::new(name),
        )
    }

    pub fn opt_opt_via<V: FromStr, T: From<V>, N: IntoName>(
        name: N,
    ) -> Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Named> {
        arg(
            arity::Optional,
            has_param::YesVia::default(),
            name_type::Named::new(name),
        )
    }

    pub fn opt_req_via<V: FromStr, T: From<V>, N: IntoName>(
        name: N,
    ) -> Arg<arity::Required, has_param::YesVia<V, T>, name_type::Named> {
        arg(
            arity::Required,
            has_param::YesVia::default(),
            name_type::Named::new(name),
        )
    }

    pub fn opt_multi_via<V: FromStr, T: From<V>, N: IntoName>(
        name: N,
    ) -> Arg<arity::Multiple, has_param::YesVia<V, T>, name_type::Named> {
        arg(
            arity::Multiple,
            has_param::YesVia::default(),
            name_type::Named::new(name),
        )
    }

    pub fn flag<N: IntoName>(name: N) -> Arg<arity::Optional, has_param::No, name_type::Named> {
        arg(arity::Optional, has_param::No, name_type::Named::new(name))
    }

    pub fn flag_count<N: IntoName>(
        name: N,
    ) -> Arg<arity::Multiple, has_param::No, name_type::Named> {
        arg(arity::Multiple, has_param::No, name_type::Named::new(name))
    }
}

pub mod low_level {
    use super::{Name, ParseError, SpecError};
    use std::collections::HashMap;
    use std::error;
    use std::vec;

    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum HasParam {
        Yes,
        No,
    }

    #[derive(Clone, Copy)]
    struct LowLevelArgRef {
        index: usize,
        has_param: HasParam,
    }

    #[derive(Default)]
    pub struct LowLevelParser {
        instance_name_to_arg_ref: HashMap<Name, LowLevelArgRef>,
        flag_count: usize,
        opt_count: usize,
    }

    pub struct LowLevelParserOutput {
        instance_name_to_arg_ref: HashMap<Name, LowLevelArgRef>,
        flags: Vec<usize>,
        opts: Vec<Vec<String>>,
        frees: vec::IntoIter<String>,
    }

    enum Token {
        Name(Name),
        Word(String),
        LongAssignment { long: String, value: String },
        ShortSequence { first: char, rest: String },
        Separator,
    }

    impl Token {
        fn parse(s: String) -> Self {
            if s == "--" {
                Token::Separator
            } else if let Some(long) = s.strip_prefix("--") {
                let assignment_split = long.splitn(2, "=").collect::<Vec<_>>();
                if assignment_split.len() == 1 {
                    Token::Name(Name::Long(long.to_string()))
                } else {
                    Token::LongAssignment {
                        long: assignment_split[0].to_string(),
                        value: assignment_split[1].to_string(),
                    }
                }
            } else if let Some(shorts) = s.strip_prefix("-") {
                match shorts.len() {
                    0 => Token::Word("-".to_string()),
                    1 => Token::Name(Name::Short(shorts.chars().next().unwrap())),
                    _ => {
                        let (first, rest) = shorts.split_at(1);
                        Token::ShortSequence {
                            first: first.chars().next().unwrap(),
                            rest: rest.to_string(),
                        }
                    }
                }
            } else {
                Token::Word(s)
            }
        }
    }

    impl LowLevelParser {
        pub fn register(&mut self, names: &[Name], has_param: HasParam) -> Result<(), SpecError> {
            let index = match has_param {
                HasParam::No => &mut self.flag_count,
                HasParam::Yes => &mut self.opt_count,
            };
            let arg_ref = LowLevelArgRef {
                index: *index,
                has_param,
            };
            for name in names {
                if self.instance_name_to_arg_ref.contains_key(name) {
                    return Err(SpecError::NameUsedMultipleTimes(name.clone()));
                }
                self.instance_name_to_arg_ref.insert(name.clone(), arg_ref);
            }
            *index += 1;
            Ok(())
        }

        pub fn parse<A: IntoIterator<Item = String>>(
            self,
            args: A,
        ) -> Result<LowLevelParserOutput, Box<dyn error::Error>> {
            let LowLevelParser {
                instance_name_to_arg_ref,
                flag_count,
                opt_count,
            } = self;
            let mut flags = vec![0; flag_count];
            let mut opts = Vec::with_capacity(opt_count);
            opts.resize_with(opt_count, Vec::new);
            let mut frees = Vec::new();
            let mut args_iter = args.into_iter();
            while let Some(token) = args_iter.next().map(Token::parse) {
                match token {
                    Token::Separator => break,
                    Token::Word(word) => frees.push(word),
                    Token::ShortSequence { first, rest } => {
                        let LowLevelArgRef { index, has_param } = instance_name_to_arg_ref
                            .get(&Name::Short(first))
                            .ok_or_else(|| ParseError::UnknownName(Name::Short(first)))?;
                        match has_param {
                            HasParam::No => {
                                flags[*index] += 1;
                                for short in rest.chars() {
                                    let LowLevelArgRef { index, has_param } =
                                        instance_name_to_arg_ref
                                            .get(&Name::Short(short))
                                            .ok_or_else(|| {
                                                ParseError::UnknownName(Name::Short(short))
                                            })?;
                                    match has_param {
                                        HasParam::No => flags[*index] += 1,
                                        HasParam::Yes => {
                                            return Err(ParseError::ArgumentLacksParameter(
                                                Name::Short(short),
                                            )
                                            .into())
                                        }
                                    }
                                }
                            }
                            HasParam::Yes => {
                                opts[*index].push(rest);
                            }
                        }
                    }
                    Token::Name(name) => {
                        let LowLevelArgRef { index, has_param } = instance_name_to_arg_ref
                            .get(&name)
                            .ok_or_else(|| ParseError::UnknownName(name.clone()))?;
                        match has_param {
                            HasParam::No => flags[*index] += 1,
                            HasParam::Yes => {
                                match Token::parse(args_iter.next().ok_or_else(|| {
                                    ParseError::ArgumentLacksParameter(name.clone())
                                })?) {
                                    Token::Word(word) => opts[*index].push(word),
                                    _ => {
                                        return Err(ParseError::ArgumentLacksParameter(name).into())
                                    }
                                }
                            }
                        }
                    }
                    Token::LongAssignment { long, value } => {
                        let name = Name::Long(long);
                        let LowLevelArgRef { index, has_param } = instance_name_to_arg_ref
                            .get(&name)
                            .ok_or_else(|| ParseError::UnknownName(name.clone()))?;
                        match has_param {
                            HasParam::No => {
                                return Err(ParseError::UnexpectedArgumentParam {
                                    name: name.clone(),
                                    value,
                                }
                                .into())
                            }
                            HasParam::Yes => opts[*index].push(value),
                        }
                    }
                }
            }
            for arg in args_iter {
                frees.push(arg);
            }
            Ok(LowLevelParserOutput {
                instance_name_to_arg_ref,
                flags,
                opts,
                frees: frees.into_iter(),
            })
        }
    }

    impl LowLevelParserOutput {
        pub fn get_flag_count(&self, names: &[Name]) -> usize {
            let LowLevelArgRef { index, has_param } =
                self.instance_name_to_arg_ref.get(&names[0]).unwrap();
            assert!(*has_param == HasParam::No);
            self.flags[*index]
        }

        pub fn get_opt_values(&self, names: &[Name]) -> &[String] {
            let LowLevelArgRef { index, has_param } =
                self.instance_name_to_arg_ref.get(&names[0]).unwrap();
            assert!(*has_param == HasParam::Yes);
            &self.opts[*index]
        }

        pub fn free_iter(&mut self) -> &mut vec::IntoIter<String> {
            &mut self.frees
        }
    }
}
