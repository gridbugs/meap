use std::marker::PhantomData;
use std::str::FromStr;

pub trait Parser: Sized {
    type Item;
}

struct Name {
    short: Option<String>,
    long: Option<String>,
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
    type Item = Vec<bool>;
}

struct MultiOpt<T: FromStr>(Opt<T>);

impl<T: FromStr> Parser for MultiOpt<T> {
    type Item = Vec<T>;
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
