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
    MissingArgument(Name),
    UnexpectedArgument { name: Name, value: String },
}

#[derive(Debug)]
pub enum SpecError {
    MultiplePositionalArguments,
    NameUsedMultipeTimes(Name),
}

pub trait Parser: Sized {
    type Item;

    fn register(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError>;

    fn parse(self, ll: &low_level::LowLevelParserOutput) -> Result<Self::Item, ParseError>;
}

// Determines how many times the opt can be passed
trait Arity {}

mod arity {
    use super::Arity;

    pub struct Required;
    pub struct Optional;
    pub struct Multiple;

    impl Arity for Required {}
    impl Arity for Optional {}
    impl Arity for Multiple {}
}

// Determines whether the opt takes a value as an argument
trait HasArg {}

mod has_arg {
    use super::HasArg;
    use std::marker::PhantomData;
    use std::str::FromStr;

    #[derive(Default)]
    pub struct Yes<T: FromStr>(PhantomData<T>);
    pub struct No;

    impl<T: FromStr> HasArg for Yes<T> {}
    impl HasArg for No {}
}

trait OptParser {
    type Item;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError>;
}

struct Opt<A: Arity, H: HasArg> {
    /// An `Opt` with no names is treated as a positional argument
    names: Vec<Name>,
    description: Option<String>,
    hint: Option<String>,
    arity: A,
    has_arg: H,
}

impl<T: FromStr> OptParser for Opt<arity::Required, has_arg::Yes<T>> {
    type Item = T;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError> {
        todo!()
    }
}

impl<T: FromStr> OptParser for Opt<arity::Optional, has_arg::Yes<T>> {
    type Item = Option<T>;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError> {
        todo!()
    }
}

impl<T: FromStr> OptParser for Opt<arity::Multiple, has_arg::Yes<T>> {
    type Item = Vec<T>;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError> {
        todo!()
    }
}

impl OptParser for Opt<arity::Optional, has_arg::No> {
    type Item = bool;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError> {
        todo!()
    }
}

impl OptParser for Opt<arity::Multiple, has_arg::No> {
    type Item = usize;

    fn parse_opt(
        &self,
        names: &[Name],
        ll: &low_level::LowLevelParserOutput,
    ) -> Result<Self::Item, ParseError> {
        todo!()
    }
}

struct Both<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> {
    parser_t: PT,
    parser_u: PU,
}

impl<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> Parser for Both<T, U, PT, PU> {
    type Item = (T, U);

    fn register(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        todo!()
    }

    fn parse(self, ll: &low_level::LowLevelParserOutput) -> Result<Self::Item, ParseError> {
        Ok((self.parser_t.parse(ll)?, self.parser_u.parse(ll)?))
    }
}

struct Map<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> {
    f: F,
    parser_t: PT,
}

impl<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> Parser for Map<T, U, F, PT> {
    type Item = U;

    fn register(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        todo!()
    }

    fn parse(self, ll: &low_level::LowLevelParserOutput) -> Result<Self::Item, ParseError> {
        Ok((self.f)(self.parser_t.parse(ll)?))
    }
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
        ShortSequence(String),
        Word(String),
        Assignment { long: String, value: String },
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
                    Token::Assignment {
                        long: assignment_split[0].to_string(),
                        value: assignment_split[1].to_string(),
                    }
                }
            } else if let Some(shorts) = s.strip_prefix("-") {
                match shorts.len() {
                    0 => Token::Word("-".to_string()),
                    1 => Token::Name(Name::Short(shorts.chars().next().unwrap())),
                    _ => Token::ShortSequence(shorts.to_string()),
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
                        return Err(SpecError::NameUsedMultipeTimes(name.clone()));
                    }
                    self.instance_name_to_arg_ref.insert(name.clone(), arg_ref);
                }
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
                    Token::ShortSequence(shorts) => {
                        for short in shorts.chars() {
                            let LowLevelArgRef { index, has_arg } = instance_name_to_arg_ref
                                .get(&Name::Short(short))
                                .ok_or_else(|| ParseError::UnknownName(Name::Short(short)))?;
                            match has_arg {
                                HasArg::No => flags[*index] += 1,
                                HasArg::Yes => {
                                    return Err(ParseError::MissingArgument(Name::Short(short)))
                                }
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
                                match Token::parse(
                                    args_iter
                                        .next()
                                        .ok_or_else(|| ParseError::MissingArgument(name.clone()))?,
                                ) {
                                    Token::Word(word) => opts[*index].push(word),
                                    _ => return Err(ParseError::MissingArgument(name)),
                                }
                            }
                        }
                    }
                    Token::Assignment { long, value } => {
                        let name = Name::Long(long);
                        let LowLevelArgRef { index, has_arg } = instance_name_to_arg_ref
                            .get(&name)
                            .ok_or_else(|| ParseError::UnknownName(name.clone()))?;
                        match has_arg {
                            HasArg::No => {
                                return Err(ParseError::UnexpectedArgument {
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
        pub fn get_flag(&self, names: &[Name]) -> usize {
            let LowLevelArgRef { index, has_arg } =
                self.instance_name_to_arg_ref.get(&names[0]).unwrap();
            assert!(*has_arg == HasArg::No);
            self.flags[*index]
        }

        pub fn get_opt(&self, names: &[Name]) -> &[String] {
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
