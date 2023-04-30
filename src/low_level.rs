use crate::parser::{Name, ParseError, SpecError};
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

pub struct LowLevelParser {
    program_name: String,
    instance_name_to_arg_ref: HashMap<Name, LowLevelArgRef>,
    flag_count: usize,
    opt_count: usize,
    has_positional_multi: bool,
    has_extra: bool,
}

pub struct LowLevelParserOutput {
    program_name: String,
    instance_name_to_arg_ref: HashMap<Name, LowLevelArgRef>,
    flags: Vec<usize>,
    opts: Vec<Vec<String>>,
    frees: vec::IntoIter<String>,
    extra: Vec<String>,
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

#[derive(Debug)]
pub enum Unique {
    PositionalMulti,
    Extra,
}

impl LowLevelParser {
    pub fn new(program_name: String) -> Self {
        Self {
            program_name,
            instance_name_to_arg_ref: HashMap::default(),
            flag_count: 0,
            opt_count: 0,
            has_positional_multi: false,
            has_extra: false,
        }
    }

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

    pub fn register_anonymous_unique(&mut self, unique: Unique) -> Result<(), SpecError> {
        match unique {
            Unique::PositionalMulti => {
                if self.has_positional_multi {
                    return Err(SpecError::RepeatedUnique(Unique::PositionalMulti));
                }
                self.has_positional_multi = true;
            }
            Unique::Extra => {
                if self.has_extra {
                    return Err(SpecError::RepeatedUnique(Unique::Extra));
                }
                self.has_extra = true;
            }
        }
        Ok(())
    }

    pub fn parse<A: IntoIterator<Item = String>>(
        self,
        args: A,
    ) -> Result<LowLevelParserOutput, Box<dyn error::Error>> {
        let LowLevelParser {
            program_name,
            instance_name_to_arg_ref,
            flag_count,
            opt_count,
            has_extra: _,
            has_positional_multi: _,
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
                                let LowLevelArgRef { index, has_param } = instance_name_to_arg_ref
                                    .get(&Name::Short(short))
                                    .ok_or_else(|| ParseError::UnknownName(Name::Short(short)))?;
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
                    let LowLevelArgRef { index, has_param } =
                        instance_name_to_arg_ref
                            .get(&name)
                            .ok_or_else(|| ParseError::UnknownName(name.clone()))?;
                    match has_param {
                        HasParam::No => flags[*index] += 1,
                        HasParam::Yes => {
                            match Token::parse(
                                args_iter.next().ok_or_else(|| {
                                    ParseError::ArgumentLacksParameter(name.clone())
                                })?,
                            ) {
                                Token::Word(word) => opts[*index].push(word),
                                _ => return Err(ParseError::ArgumentLacksParameter(name).into()),
                            }
                        }
                    }
                }
                Token::LongAssignment { long, value } => {
                    let name = Name::Long(long);
                    let LowLevelArgRef { index, has_param } =
                        instance_name_to_arg_ref
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
        Ok(LowLevelParserOutput {
            program_name,
            instance_name_to_arg_ref,
            flags,
            opts,
            frees: frees.into_iter(),
            extra: args_iter.collect(),
        })
    }
}

impl LowLevelParserOutput {
    pub fn program_name(&self) -> &str {
        self.program_name.as_str()
    }

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

    pub fn extra(&self) -> &[String] {
        &self.extra
    }
}
