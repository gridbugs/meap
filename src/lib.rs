use std::env;
use std::str::FromStr;

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Name {
    Long(String),
    Short(char),
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedPositionalArgument(String),
    UnknownName(Name),
    MissingArgumentValue(Name),
    UnexpectedArgumentValue {
        name: Name,
        value: String,
    },
    MissingRequiredArgument(Vec<Name>),
    ExpectedOneArgumentValue {
        names: Vec<Name>,
        values: Vec<String>,
    },
    UnableToParseArgumentValue {
        names: Vec<Name>,
        value: String,
    },
    ExpectedOneFlag {
        names: Vec<Name>,
        count: usize,
    },
}

#[derive(Debug)]
pub enum SpecError {
    MultiplePositionalArguments,
    NameUsedMultipleTimes(Name),
    FlagWithNoNames,
}

pub trait Parser: Sized {
    type Item;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError>;

    fn parse_low_level(
        self,
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError>;

    fn parse_args<A: IntoIterator<Item = String>>(self, args: A) -> Result<Self::Item, ParseError> {
        let mut low_level_parser = low_level::LowLevelParser::default();
        self.register_low_level(&mut low_level_parser).unwrap();
        let low_level_output = low_level_parser.parse(args)?;
        self.parse_low_level(&low_level_output)
    }

    fn parse_env(self) -> Result<Self::Item, ParseError> {
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

// Determines whether the opt takes a value as an argument
pub trait HasArg {
    fn low_level() -> low_level::HasArg;
}

pub mod has_arg {
    use super::{low_level, HasArg};
    use std::marker::PhantomData;
    use std::str::FromStr;

    pub struct YesVia<V: FromStr, T: From<V>>(PhantomData<(V, T)>);
    pub struct No;

    impl<V: FromStr, T: From<V>> HasArg for YesVia<V, T> {
        fn low_level() -> low_level::HasArg {
            low_level::HasArg::Yes
        }
    }
    impl HasArg for No {
        fn low_level() -> low_level::HasArg {
            low_level::HasArg::No
        }
    }

    impl<V: FromStr, T: From<V>> Default for YesVia<V, T> {
        fn default() -> Self {
            Self(PhantomData)
        }
    }
}

pub trait OptParser {
    type OptItem;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::OptItem, ParseError>;
}

pub struct Opt<A: Arity, H: HasArg> {
    /// An `Opt` with no names is treated as a positional argument
    pub names: Vec<Name>,
    pub description: Option<String>,
    pub hint: Option<String>,
    pub arity: A,
    pub has_arg: H,
}

impl<A: Arity, H: HasArg> Opt<A, H> {
    pub fn name(mut self, name: Name) -> Self {
        self.names.push(name);
        self
    }
    pub fn long<S: AsRef<str>>(self, long: S) -> Self {
        self.name(Name::Long(long.as_ref().to_string()))
    }
    pub fn short(self, short: char) -> Self {
        self.name(Name::Short(short))
    }
    pub fn description<S: AsRef<str>>(mut self, description: S) -> Self {
        self.description = Some(description.as_ref().to_string());
        self
    }
    pub fn hint<S: AsRef<str>>(mut self, hint: S) -> Self {
        self.hint = Some(hint.as_ref().to_string());
        self
    }
    pub fn l<S: AsRef<str>>(self, long: S) -> Self {
        self.long(long)
    }
    pub fn s(self, short: char) -> Self {
        self.short(short)
    }
    pub fn d<S: AsRef<str>>(self, description: S) -> Self {
        self.description(description)
    }
    pub fn h<S: AsRef<str>>(self, hint: S) -> Self {
        self.hint(hint)
    }
}

pub mod prelude {
    pub use super::Parser;
    use super::*;

    pub fn opt<A: Arity, H: HasArg>(arity: A, has_arg: H) -> Opt<A, H> {
        Opt {
            names: Vec::new(),
            description: None,
            hint: None,
            arity,
            has_arg,
        }
    }

    pub fn opt_opt<T: FromStr>() -> Opt<arity::Optional, has_arg::YesVia<T, T>> {
        opt(arity::Optional, has_arg::YesVia::default())
    }

    pub fn opt_req<T: FromStr>() -> Opt<arity::Required, has_arg::YesVia<T, T>> {
        opt(arity::Required, has_arg::YesVia::default())
    }

    pub fn opt_multi<T: FromStr>() -> Opt<arity::Multiple, has_arg::YesVia<T, T>> {
        opt(arity::Multiple, has_arg::YesVia::default())
    }

    pub fn opt_opt_via<V: FromStr, T: From<V>>() -> Opt<arity::Optional, has_arg::YesVia<V, T>> {
        opt(arity::Optional, has_arg::YesVia::default())
    }

    pub fn opt_req_via<V: FromStr, T: From<V>>() -> Opt<arity::Required, has_arg::YesVia<V, T>> {
        opt(arity::Required, has_arg::YesVia::default())
    }

    pub fn opt_multi_via<V: FromStr, T: From<V>>() -> Opt<arity::Multiple, has_arg::YesVia<V, T>> {
        opt(arity::Multiple, has_arg::YesVia::default())
    }

    pub fn flag() -> Opt<arity::Optional, has_arg::No> {
        opt(arity::Optional, has_arg::No)
    }

    pub fn flag_count() -> Opt<arity::Multiple, has_arg::No> {
        opt(arity::Multiple, has_arg::No)
    }
}

impl<V: FromStr, T: From<V>> OptParser for Opt<arity::Required, has_arg::YesVia<V, T>> {
    type OptItem = T;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::OptItem, ParseError> {
        let values = ll.get_opt_values(names);
        match values.len() {
            0 => Err(ParseError::MissingRequiredArgument(names.to_vec())),
            1 => Ok(T::from(values[0].parse().map_err(|_| {
                ParseError::UnableToParseArgumentValue {
                    names: names.to_vec(),
                    value: values[0].clone(),
                }
            })?)),
            _ => Err(ParseError::ExpectedOneArgumentValue {
                names: names.to_vec(),
                values: values.to_vec(),
            }),
        }
    }
}

impl<V: FromStr, T: From<V>> OptParser for Opt<arity::Optional, has_arg::YesVia<V, T>> {
    type OptItem = Option<T>;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::OptItem, ParseError> {
        let values = ll.get_opt_values(names);
        match values.len() {
            0 => Ok(None),
            1 => Ok(Some(T::from(values[0].parse().map_err(|_| {
                ParseError::UnableToParseArgumentValue {
                    names: names.to_vec(),
                    value: values[0].clone(),
                }
            })?))),
            _ => Err(ParseError::ExpectedOneArgumentValue {
                names: names.to_vec(),
                values: values.to_vec(),
            }),
        }
    }
}

impl<V: FromStr, T: From<V>> OptParser for Opt<arity::Multiple, has_arg::YesVia<V, T>> {
    type OptItem = Vec<T>;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::OptItem, ParseError> {
        let values = ll.get_opt_values(names);
        let mut ret = Vec::with_capacity(values.len());
        for v in values {
            ret.push(T::from(v.parse().map_err(|_| {
                ParseError::UnableToParseArgumentValue {
                    names: names.to_vec(),
                    value: v.clone(),
                }
            })?));
        }
        Ok(ret)
    }
}

impl OptParser for Opt<arity::Optional, has_arg::No> {
    type OptItem = bool;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::OptItem, ParseError> {
        match ll.get_flag_count(names) {
            0 => Ok(false),
            1 => Ok(true),
            count => Err(ParseError::ExpectedOneFlag {
                names: names.to_vec(),
                count,
            }),
        }
    }
}

impl OptParser for Opt<arity::Multiple, has_arg::No> {
    type OptItem = usize;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::OptItem, ParseError> {
        Ok(ll.get_flag_count(names))
    }
}

impl<A: Arity, H: HasArg> Parser for Opt<A, H>
where
    Self: OptParser,
{
    type Item = <Self as OptParser>::OptItem;

    fn register_low_level(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        let has_arg = H::low_level();
        if let low_level::HasArg::No = has_arg {
            if self.names.is_empty() {
                return Err(SpecError::FlagWithNoNames);
            }
        }
        ll.register(&self.names, has_arg)
    }

    fn parse_low_level(
        self,
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError> {
        self.parse_opt(&self.names, ll)
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
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError> {
        Ok((
            self.parser_t.parse_low_level(ll)?,
            self.parser_u.parse_low_level(ll)?,
        ))
    }
}

impl<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> Both<T, U, PT, PU> {
    pub fn parse_env(self) -> Result<(T, U), ParseError> {
        <Self as Parser>::parse_env(self)
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
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError> {
        Ok((self.f)(self.parser_t.parse_low_level(ll)?))
    }
}

impl<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> Map<T, U, F, PT> {
    pub fn parse_env(self) -> Result<U, ParseError> {
        <Self as Parser>::parse_env(self)
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

pub mod low_level {
    use super::{Name, ParseError, SpecError};
    use std::collections::HashMap;

    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum HasArg {
        Yes,
        No,
    }

    #[derive(Clone, Copy)]
    struct LowLevelArgRef {
        index: usize,
        has_arg: HasArg,
    }

    #[derive(Default)]
    pub struct LowLevelParser {
        instance_name_to_arg_ref: HashMap<Name, LowLevelArgRef>,
        flag_count: usize,
        opt_count: usize,
        allow_frees: bool,
    }

    pub struct LowLevelParserOutput {
        instance_name_to_arg_ref: HashMap<Name, LowLevelArgRef>,
        flags: Vec<usize>,
        opts: Vec<Vec<String>>,
        frees: Vec<String>,
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
        pub fn register(&mut self, names: &[Name], has_arg: HasArg) -> Result<(), SpecError> {
            if names.is_empty() {
                assert!(has_arg == HasArg::Yes);
                if self.allow_frees {
                    return Err(SpecError::MultiplePositionalArguments);
                }
                self.allow_frees = true;
            } else {
                let index = match has_arg {
                    HasArg::No => &mut self.flag_count,
                    HasArg::Yes => &mut self.opt_count,
                };
                let arg_ref = LowLevelArgRef {
                    index: *index,
                    has_arg,
                };
                for name in names {
                    if self.instance_name_to_arg_ref.contains_key(name) {
                        return Err(SpecError::NameUsedMultipleTimes(name.clone()));
                    }
                    self.instance_name_to_arg_ref.insert(name.clone(), arg_ref);
                }
                *index += 1;
            }
            Ok(())
        }

        pub fn parse<A: IntoIterator<Item = String>>(
            self,
            args: A,
        ) -> Result<LowLevelParserOutput, ParseError> {
            let LowLevelParser {
                instance_name_to_arg_ref,
                flag_count,
                opt_count,
                allow_frees,
            } = self;
            let mut flags = vec![0; flag_count];
            let mut opts = Vec::with_capacity(opt_count);
            opts.resize_with(opt_count, Vec::new);
            let mut frees = Vec::new();
            let mut args_iter = args.into_iter();
            while let Some(token) = args_iter.next().map(Token::parse) {
                match token {
                    Token::Separator => break,
                    Token::Word(word) => {
                        if allow_frees {
                            frees.push(word);
                        } else {
                            return Err(ParseError::UnexpectedPositionalArgument(word));
                        }
                    }
                    Token::ShortSequence { first, rest } => {
                        let LowLevelArgRef { index, has_arg } = instance_name_to_arg_ref
                            .get(&Name::Short(first))
                            .ok_or_else(|| ParseError::UnknownName(Name::Short(first)))?;
                        match has_arg {
                            HasArg::No => {
                                flags[*index] += 1;
                                for short in rest.chars() {
                                    let LowLevelArgRef { index, has_arg } =
                                        instance_name_to_arg_ref
                                            .get(&Name::Short(short))
                                            .ok_or_else(|| {
                                                ParseError::UnknownName(Name::Short(short))
                                            })?;
                                    match has_arg {
                                        HasArg::No => flags[*index] += 1,
                                        HasArg::Yes => {
                                            return Err(ParseError::MissingArgumentValue(
                                                Name::Short(short),
                                            ))
                                        }
                                    }
                                }
                            }
                            HasArg::Yes => {
                                opts[*index].push(rest);
                            }
                        }
                    }
                    Token::Name(name) => {
                        let LowLevelArgRef { index, has_arg } = instance_name_to_arg_ref
                            .get(&name)
                            .ok_or_else(|| ParseError::UnknownName(name.clone()))?;
                        match has_arg {
                            HasArg::No => flags[*index] += 1,
                            HasArg::Yes => {
                                match Token::parse(args_iter.next().ok_or_else(|| {
                                    ParseError::MissingArgumentValue(name.clone())
                                })?) {
                                    Token::Word(word) => opts[*index].push(word),
                                    _ => return Err(ParseError::MissingArgumentValue(name)),
                                }
                            }
                        }
                    }
                    Token::LongAssignment { long, value } => {
                        let name = Name::Long(long);
                        let LowLevelArgRef { index, has_arg } = instance_name_to_arg_ref
                            .get(&name)
                            .ok_or_else(|| ParseError::UnknownName(name.clone()))?;
                        match has_arg {
                            HasArg::No => {
                                return Err(ParseError::UnexpectedArgumentValue {
                                    name: name.clone(),
                                    value,
                                })
                            }
                            HasArg::Yes => opts[*index].push(value),
                        }
                    }
                }
            }
            if allow_frees {
                for arg in args_iter {
                    frees.push(arg);
                }
            } else if let Some(arg) = args_iter.next() {
                return Err(ParseError::UnexpectedPositionalArgument(arg));
            }
            Ok(LowLevelParserOutput {
                instance_name_to_arg_ref,
                flags,
                opts,
                frees,
            })
        }
    }

    impl LowLevelParserOutput {
        pub fn get_flag_count(&self, names: &[Name]) -> usize {
            let LowLevelArgRef { index, has_arg } =
                self.instance_name_to_arg_ref.get(&names[0]).unwrap();
            assert!(*has_arg == HasArg::No);
            self.flags[*index]
        }

        pub fn get_opt_values(&self, names: &[Name]) -> &[String] {
            if let Some(name) = names.first() {
                let LowLevelArgRef { index, has_arg } =
                    self.instance_name_to_arg_ref.get(name).unwrap();
                assert!(*has_arg == HasArg::Yes);
                &self.opts[*index]
            } else {
                &self.frees
            }
        }
    }
}
