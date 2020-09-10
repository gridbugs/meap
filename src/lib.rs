use std::marker::PhantomData;
use std::str::FromStr;

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Switch {
    Long(String),
    Short(char),
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedFreeArgument(String),
    UnknownSwitch(Switch),
    MissingArgument(Switch),
    OptInFlagSequence(char),
    ExpectedAtMostOne { name: Option<Name>, found: usize },
    FailedToParse { name: Option<Name>, value: String },
}

#[derive(Debug)]
pub enum SpecError {
    MultipleFreeArguments,
    SwitchUsedMultipeTimes(Switch),
}

#[derive(Debug, Clone)]
pub enum Name {
    Single(Switch),
    Double { short: char, long: String },
}

impl Name {
    fn switch(&self) -> Switch {
        match self {
            Self::Single(switch) => switch.clone(),
            Self::Double { short, .. } => Switch::Short(*short),
        }
    }
}

pub trait Parser: Sized {
    type Item;

    fn traverse<F: FnMut(Option<&Name>, low_level::FlagOrOpt)>(&self, f: F);

    fn register(&self, ll: &mut low_level::LowLevelParser) -> Result<(), SpecError> {
        let mut result = Ok(());
        self.traverse(|maybe_name, flag_or_opt| {
            if result.is_ok() {
                result = ll.register(maybe_name, flag_or_opt);
            }
        });
        result
    }

    fn parse(self, ll: &low_level::LowLevelParserOutput) -> Result<Self::Item, ParseError>;
}

struct Flag {
    name: Name,
    description: Option<String>,
}

struct Opt<T: FromStr> {
    name: Option<Name>,
    description: Option<String>,
    hint: Option<String>,
    typ: PhantomData<T>,
}

impl Parser for Flag {
    type Item = bool;

    fn traverse<F: FnMut(Option<&Name>, low_level::FlagOrOpt)>(&self, mut f: F) {
        f(Some(&self.name), low_level::FlagOrOpt::Flag);
    }

    fn parse(self, ll: &low_level::LowLevelParserOutput) -> Result<Self::Item, ParseError> {
        let output = ll.get_flag(&self.name.switch());
        if output > 1 {
            return Err(ParseError::ExpectedAtMostOne {
                found: output,
                name: Some(self.name.clone()),
            });
        }
        Ok(output == 1)
    }
}

impl<T: FromStr> Parser for Opt<T> {
    type Item = Option<T>;

    fn traverse<F: FnMut(Option<&Name>, low_level::FlagOrOpt)>(&self, mut f: F) {
        f(self.name.as_ref(), low_level::FlagOrOpt::Opt);
    }

    fn parse(self, ll: &low_level::LowLevelParserOutput) -> Result<Self::Item, ParseError> {
        let output = if let Some(name) = self.name.as_ref() {
            ll.get_opt(&name.switch())
        } else {
            ll.get_free()
        };
        if output.len() > 1 {
            return Err(ParseError::ExpectedAtMostOne {
                found: output.len() as usize,
                name: self.name.clone(),
            });
        }
        if let Some(first) = output.first() {
            Ok(Some(first.parse().map_err(|_| {
                ParseError::FailedToParse {
                    name: self.name.clone(),
                    value: first.clone(),
                }
            })?))
        } else {
            Ok(None)
        }
    }
}

struct Both<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> {
    parser_t: PT,
    parser_u: PU,
}

impl<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> Parser for Both<T, U, PT, PU> {
    type Item = (T, U);

    fn traverse<F: FnMut(Option<&Name>, low_level::FlagOrOpt)>(&self, mut f: F) {
        self.parser_t.traverse(&mut f);
        self.parser_u.traverse(&mut f);
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

    fn traverse<G: FnMut(Option<&Name>, low_level::FlagOrOpt)>(&self, mut f: G) {
        self.parser_t.traverse(&mut f);
    }

    fn parse(self, ll: &low_level::LowLevelParserOutput) -> Result<Self::Item, ParseError> {
        Ok((self.f)(self.parser_t.parse(ll)?))
    }
}

pub mod low_level {
    use super::{Name, ParseError, SpecError, Switch};
    use std::collections::HashMap;

    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum FlagOrOpt {
        Flag,
        Opt,
    }

    #[derive(Clone, Copy)]
    struct LowLevelArgRef {
        index: usize,
        flag_or_opt: FlagOrOpt,
    }

    #[derive(Default)]
    pub struct LowLevelParser {
        instance_name_to_arg_ref: HashMap<Switch, LowLevelArgRef>,
        flag_count: usize,
        opt_count: usize,
        allow_frees: bool,
    }

    pub struct LowLevelParserOutput {
        instance_name_to_arg_ref: HashMap<Switch, LowLevelArgRef>,
        flags: Vec<usize>,
        opts: Vec<Vec<String>>,
        frees: Vec<String>,
    }

    enum Token {
        Switch(Switch),
        ShortSequence(String),
        Word(String),
        Separator,
    }

    impl Token {
        fn parse(s: String) -> Self {
            if s == "--" {
                Token::Separator
            } else if let Some(long) = s.strip_prefix("--") {
                Token::Switch(Switch::Long(long.to_string()))
            } else if let Some(shorts) = s.strip_prefix("-") {
                match shorts.len() {
                    0 => Token::Word("-".to_string()),
                    1 => Token::Switch(Switch::Short(shorts.chars().next().unwrap())),
                    _ => Token::ShortSequence(shorts.to_string()),
                }
            } else {
                Token::Word(s)
            }
        }
    }

    impl LowLevelParser {
        fn register_switch(
            instance_name_to_arg_ref: &mut HashMap<Switch, LowLevelArgRef>,
            switch: &Switch,
            arg_ref: LowLevelArgRef,
        ) -> Result<(), SpecError> {
            if instance_name_to_arg_ref.contains_key(switch) {
                return Err(SpecError::SwitchUsedMultipeTimes(switch.clone()));
            }
            instance_name_to_arg_ref.insert(switch.clone(), arg_ref);
            Ok(())
        }
        pub fn register(
            &mut self,
            name: Option<&Name>,
            flag_or_opt: FlagOrOpt,
        ) -> Result<(), SpecError> {
            match name {
                None => {
                    assert!(flag_or_opt == FlagOrOpt::Opt);
                    if self.allow_frees {
                        return Err(SpecError::MultipleFreeArguments);
                    }
                    self.allow_frees = true;
                }
                Some(name) => {
                    let index = match flag_or_opt {
                        FlagOrOpt::Flag => &mut self.flag_count,
                        FlagOrOpt::Opt => &mut self.opt_count,
                    };
                    let arg_ref = LowLevelArgRef {
                        index: *index,
                        flag_or_opt,
                    };
                    match name {
                        Name::Single(switch) => Self::register_switch(
                            &mut self.instance_name_to_arg_ref,
                            switch,
                            arg_ref,
                        )?,
                        Name::Double { short, long } => {
                            Self::register_switch(
                                &mut self.instance_name_to_arg_ref,
                                &Switch::Short(*short),
                                arg_ref,
                            )?;
                            Self::register_switch(
                                &mut self.instance_name_to_arg_ref,
                                &Switch::Long(long.clone()),
                                arg_ref,
                            )?;
                        }
                    }
                    *index += 1;
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
                            return Err(ParseError::UnexpectedFreeArgument(word));
                        }
                    }
                    Token::ShortSequence(shorts) => {
                        for short in shorts.chars() {
                            let LowLevelArgRef { index, flag_or_opt } = instance_name_to_arg_ref
                                .get(&Switch::Short(short))
                                .ok_or_else(|| ParseError::UnknownSwitch(Switch::Short(short)))?;
                            match flag_or_opt {
                                FlagOrOpt::Flag => flags[*index] += 1,
                                FlagOrOpt::Opt => return Err(ParseError::OptInFlagSequence(short)),
                            }
                        }
                    }
                    Token::Switch(switch) => {
                        let LowLevelArgRef { index, flag_or_opt } = instance_name_to_arg_ref
                            .get(&switch)
                            .ok_or_else(|| ParseError::UnknownSwitch(switch.clone()))?;
                        match flag_or_opt {
                            FlagOrOpt::Flag => flags[*index] += 1,
                            FlagOrOpt::Opt => {
                                match Token::parse(
                                    args_iter.next().ok_or_else(|| {
                                        ParseError::MissingArgument(switch.clone())
                                    })?,
                                ) {
                                    Token::Word(word) => opts[*index].push(word),
                                    _ => return Err(ParseError::MissingArgument(switch)),
                                }
                            }
                        }
                    }
                }
            }
            if allow_frees {
                for arg in args_iter {
                    frees.push(arg);
                }
            } else if let Some(arg) = args_iter.next() {
                return Err(ParseError::UnexpectedFreeArgument(arg));
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
        pub fn get_flag(&self, switch: &Switch) -> usize {
            let LowLevelArgRef { index, flag_or_opt } =
                self.instance_name_to_arg_ref.get(switch).unwrap();
            assert!(*flag_or_opt == FlagOrOpt::Flag);
            self.flags[*index]
        }

        pub fn get_opt(&self, switch: &Switch) -> &[String] {
            let LowLevelArgRef { index, flag_or_opt } =
                self.instance_name_to_arg_ref.get(switch).unwrap();
            assert!(*flag_or_opt == FlagOrOpt::Opt);
            &self.opts[*index]
        }

        pub fn get_free(&self) -> &[String] {
            &self.frees
        }
    }
}
