use std::collections::HashMap;
use std::fmt::Display;
use std::marker::PhantomData;
use std::str::FromStr;

#[derive(Debug)]
pub enum ParseError {
    UnexpectedFreeArgument(String),
    UnknownSwitch(Switch),
    MissingArgument(Switch),
    OptInFlagSequence(char),
}

enum Name {
    Single(Switch),
    Both { short: char, long: String },
    Free,
}

pub trait Parser: Sized {
    type Item;
}

struct Flag {
    name: Name,
    description: Option<String>,
}

struct Opt<T: FromStr> {
    name: Name,
    description: Option<String>,
    hint: Option<String>,
    typ: PhantomData<T>,
}

impl Parser for Flag {
    type Item = bool;
}

impl<T: FromStr> Parser for Opt<T> {
    type Item = Option<T>;
}

struct Req<T: FromStr>(Opt<T>);

impl<T: FromStr> Parser for Req<T> {
    type Item = T;
}

struct MulitFlag(Flag);

impl Parser for MulitFlag {
    type Item = u32;
}

struct MultiOpt<T: FromStr>(Opt<T>);

impl<T: FromStr> Parser for MultiOpt<T> {
    type Item = Vec<T>;
}

struct WithDefault<T: FromStr + Display> {
    opt: Opt<T>,
    default: T,
}

impl<T: FromStr + Display> Parser for WithDefault<T> {
    type Item = T;
}

struct WithDefaultLazy<T: FromStr, F: FnOnce() -> T> {
    opt: Opt<T>,
    default: F,
    description: String,
}

impl<T: FromStr, F: FnOnce() -> T> Parser for WithDefaultLazy<T, F> {
    type Item = T;
}

struct Both<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> {
    parser_t: PT,
    parser_u: PU,
}

impl<T, U, PT: Parser<Item = T>, PU: Parser<Item = U>> Parser for Both<T, U, PT, PU> {
    type Item = (T, U);
}

struct Map<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> {
    f: F,
    parser_t: PT,
}

impl<T, U, F: FnOnce(T) -> U, PT: Parser<Item = T>> Parser for Map<T, U, F, PT> {
    type Item = U;
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FlagOrOpt {
    Flag,
    Opt,
}

struct LowLevelArgRef {
    index: usize,
    flag_or_opt: FlagOrOpt,
}

#[derive(Default)]
struct LowLevelParser {
    instance_name_to_arg_ref: HashMap<Switch, LowLevelArgRef>,
    flag_count: usize,
    opt_count: usize,
    allow_frees: bool,
}

struct LowLevelParserOutput {
    instance_name_to_arg_ref: HashMap<Switch, LowLevelArgRef>,
    flags: Vec<u32>,
    opts: Vec<Vec<String>>,
    frees: Vec<String>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Switch {
    Long(String),
    Short(char),
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
    fn parse<A: IntoIterator<Item = String>>(
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
                                args_iter
                                    .next()
                                    .ok_or_else(|| ParseError::MissingArgument(switch.clone()))?,
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
    fn get_flag(&self, switch: &Switch) -> u32 {
        let LowLevelArgRef { index, flag_or_opt } =
            self.instance_name_to_arg_ref.get(switch).unwrap();
        assert!(*flag_or_opt == FlagOrOpt::Flag);
        self.flags[*index]
    }

    fn get_opt(&self, switch: &Switch) -> &[String] {
        let LowLevelArgRef { index, flag_or_opt } =
            self.instance_name_to_arg_ref.get(switch).unwrap();
        assert!(*flag_or_opt == FlagOrOpt::Opt);
        &self.opts[*index]
    }
}
