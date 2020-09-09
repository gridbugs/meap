use std::collections::HashMap;
use std::fmt::Display;
use std::marker::PhantomData;
use std::str::FromStr;

#[derive(Debug)]
pub enum ParseError {
    UnexpectedFreeArgument(String),
    UnknownLong(String),
    UnknownShort(char),
    MissingArgumentForLong(String),
    MissingArgumentForShort(char),
    OptInFlagSequence(char),
}

enum Name {
    Short(char),
    Long(String),
    Both { short: char, long: String },
    Free,
}

impl Name {
    fn instance_name(&self) -> InstanceName {
        match self {
            Self::Short(short) => InstanceName::Short(*short),
            Self::Long(long) => InstanceName::Long(long.clone()),
            Self::Both { short, .. } => InstanceName::Short(*short),
            Self::Free => InstanceName::Free,
        }
    }
}

pub trait Parser: Sized {
    type Item;
}

struct Flag {
    name: Name,
    description: Option<String>,
}

impl Parser for Flag {
    type Item = bool;
}

struct Opt<T: FromStr> {
    name: Name,
    description: Option<String>,
    hint: Option<String>,
    typ: PhantomData<T>,
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

#[derive(Hash, PartialEq, Eq)]
enum InstanceName {
    Short(char),
    Long(String),
    Free,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FlagOrOpt {
    Flag,
    Opt,
}

#[derive(Clone, Copy)]
struct LowLevelArgRef {
    index: usize,
    flag_or_opt: FlagOrOpt,
}

#[derive(Default)]
struct LowLevelParser {
    instance_name_to_arg_ref: HashMap<InstanceName, LowLevelArgRef>,
    flag_count: usize,
    opt_count: usize,
}

struct LowLevelParserOutput {
    instance_name_to_arg_ref: HashMap<InstanceName, LowLevelArgRef>,
    flags: Vec<u32>,
    opts: Vec<Vec<String>>,
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
        } = self;
        let mut flags = vec![0; flag_count];
        let mut opts = Vec::with_capacity(opt_count);
        opts.resize_with(opt_count, Vec::new);
        let mut args_iter = args.into_iter();
        let free_opt_index = instance_name_to_arg_ref.get(&InstanceName::Free).map(
            |&LowLevelArgRef { index, flag_or_opt }| {
                debug_assert!(flag_or_opt == FlagOrOpt::Opt);
                index
            },
        );
        let mut current_argument_instance_name = InstanceName::Free;
        let mut interpret_next_free_as = free_opt_index;
        while let Some(arg) = args_iter.next() {
            if arg == "--" {
                break;
            }
            if let Some(long) = arg.strip_prefix("--") {
                match current_argument_instance_name {
                    InstanceName::Long(long) => {
                        return Err(ParseError::MissingArgumentForLong(long))
                    }
                    InstanceName::Short(short) => {
                        return Err(ParseError::MissingArgumentForShort(short))
                    }
                    InstanceName::Free => (),
                }
                let instance_name = InstanceName::Long(long.to_string());
                let LowLevelArgRef { index, flag_or_opt } = instance_name_to_arg_ref
                    .get(&instance_name)
                    .ok_or_else(|| ParseError::UnknownLong(long.to_string()))?;
                match flag_or_opt {
                    FlagOrOpt::Flag => flags[*index] += 1,
                    FlagOrOpt::Opt => {
                        current_argument_instance_name = instance_name;
                        interpret_next_free_as = Some(*index);
                    }
                }
                continue;
            } else if let Some(shorts) = arg.strip_prefix("-") {
                match shorts.len() {
                    0 => (),
                    1 => {
                        match current_argument_instance_name {
                            InstanceName::Long(long) => {
                                return Err(ParseError::MissingArgumentForLong(long))
                            }
                            InstanceName::Short(short) => {
                                return Err(ParseError::MissingArgumentForShort(short))
                            }
                            InstanceName::Free => (),
                        }
                        let short = shorts.chars().next().unwrap();
                        let instance_name = InstanceName::Short(short);
                        let LowLevelArgRef { index, flag_or_opt } = instance_name_to_arg_ref
                            .get(&instance_name)
                            .ok_or_else(|| ParseError::UnknownShort(short))?;
                        match flag_or_opt {
                            FlagOrOpt::Flag => flags[*index] += 1,
                            FlagOrOpt::Opt => {
                                current_argument_instance_name = instance_name;
                                interpret_next_free_as = Some(*index);
                            }
                        }
                        continue;
                    }
                    _multiple => {
                        match current_argument_instance_name {
                            InstanceName::Long(long) => {
                                return Err(ParseError::MissingArgumentForLong(long))
                            }
                            InstanceName::Short(short) => {
                                return Err(ParseError::MissingArgumentForShort(short))
                            }
                            InstanceName::Free => (),
                        }
                        for short in shorts.chars() {
                            let instance_name = InstanceName::Short(short);
                            let LowLevelArgRef { index, flag_or_opt } = instance_name_to_arg_ref
                                .get(&instance_name)
                                .ok_or_else(|| ParseError::UnknownShort(short))?;
                            match flag_or_opt {
                                FlagOrOpt::Flag => flags[*index] += 1,
                                FlagOrOpt::Opt => return Err(ParseError::OptInFlagSequence(short)),
                            }
                        }
                        continue;
                    }
                }
            }
            if let Some(index) = interpret_next_free_as {
                opts[index].push(arg);
            } else {
                return Err(ParseError::UnexpectedFreeArgument(arg));
            }
            current_argument_instance_name = InstanceName::Free;
            interpret_next_free_as = free_opt_index;
        }
        match current_argument_instance_name {
            InstanceName::Long(long) => return Err(ParseError::MissingArgumentForLong(long)),
            InstanceName::Short(short) => return Err(ParseError::MissingArgumentForShort(short)),
            InstanceName::Free => (),
        }
        if let Some(index) = free_opt_index {
            for arg in args_iter {
                opts[index].push(arg);
            }
        } else if let Some(arg) = args_iter.next() {
            return Err(ParseError::UnexpectedFreeArgument(arg));
        }
        Ok(LowLevelParserOutput {
            instance_name_to_arg_ref,
            flags,
            opts,
        })
    }
}

impl LowLevelParserOutput {
    fn get_flag(&self, name: &Name) -> u32 {
        let LowLevelArgRef { index, flag_or_opt } = self
            .instance_name_to_arg_ref
            .get(&name.instance_name())
            .unwrap();
        debug_assert!(*flag_or_opt == FlagOrOpt::Flag);
        self.flags[*index]
    }

    fn get_opt(&self, name: &Name) -> &[String] {
        let LowLevelArgRef { index, flag_or_opt } = self
            .instance_name_to_arg_ref
            .get(&name.instance_name())
            .unwrap();
        debug_assert!(*flag_or_opt == FlagOrOpt::Opt);
        &self.opts[*index]
    }
}
