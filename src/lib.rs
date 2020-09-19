pub mod low_level;
pub mod parser;

pub use parser::Parser;
pub type ArgsMap<T> = parser::Id<T>;

pub mod prelude {
    pub use crate::parser::Parser;
    use crate::parser::*;
    use std::str::FromStr;

    pub fn pos_opt<T: FromStr>(
        hint: &str,
    ) -> Arg<arity::Optional, has_param::YesVia<T, T>, name_type::Positional> {
        Arg::new(
            arity::Optional,
            has_param::YesVia::new(hint),
            name_type::Positional,
        )
    }

    pub fn pos_req<T: FromStr>(
        hint: &str,
    ) -> Arg<arity::Required, has_param::YesVia<T, T>, name_type::Positional> {
        Arg::new(
            arity::Required,
            has_param::YesVia::new(hint),
            name_type::Positional,
        )
    }

    pub fn pos_multi<T: FromStr>(
        hint: &str,
    ) -> Arg<arity::Multiple, has_param::YesVia<T, T>, name_type::Positional> {
        Arg::new(
            arity::Multiple,
            has_param::YesVia::new(hint),
            name_type::Positional,
        )
    }

    pub fn pos_opt_via<V: FromStr, T: From<V>>(
        hint: &str,
    ) -> Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Positional> {
        Arg::new(
            arity::Optional,
            has_param::YesVia::new(hint),
            name_type::Positional,
        )
    }

    pub fn pos_req_via<V: FromStr, T: From<V>>(
        hint: &str,
    ) -> Arg<arity::Required, has_param::YesVia<V, T>, name_type::Positional> {
        Arg::new(
            arity::Required,
            has_param::YesVia::new(hint),
            name_type::Positional,
        )
    }

    pub fn pos_multi_via<V: FromStr, T: From<V>>(
        hint: &str,
    ) -> Arg<arity::Multiple, has_param::YesVia<V, T>, name_type::Positional> {
        Arg::new(
            arity::Multiple,
            has_param::YesVia::new(hint),
            name_type::Positional,
        )
    }

    pub fn opt_opt<T: FromStr, N: IntoName>(
        hint: &str,
        name: N,
    ) -> Arg<arity::Optional, has_param::YesVia<T, T>, name_type::Named> {
        Arg::new(
            arity::Optional,
            has_param::YesVia::new(hint),
            name_type::Named::new(name),
        )
    }

    pub fn opt_req<T: FromStr, N: IntoName>(
        hint: &str,
        name: N,
    ) -> Arg<arity::Required, has_param::YesVia<T, T>, name_type::Named> {
        Arg::new(
            arity::Required,
            has_param::YesVia::new(hint),
            name_type::Named::new(name),
        )
    }

    pub fn opt_multi<T: FromStr, N: IntoName>(
        hint: &str,
        name: N,
    ) -> Arg<arity::Multiple, has_param::YesVia<T, T>, name_type::Named> {
        Arg::new(
            arity::Multiple,
            has_param::YesVia::new(hint),
            name_type::Named::new(name),
        )
    }

    pub fn opt_opt_via<V: FromStr, T: From<V>, N: IntoName>(
        hint: &str,
        name: N,
    ) -> Arg<arity::Optional, has_param::YesVia<V, T>, name_type::Named> {
        Arg::new(
            arity::Optional,
            has_param::YesVia::new(hint),
            name_type::Named::new(name),
        )
    }

    pub fn opt_req_via<V: FromStr, T: From<V>, N: IntoName>(
        hint: &str,
        name: N,
    ) -> Arg<arity::Required, has_param::YesVia<V, T>, name_type::Named> {
        Arg::new(
            arity::Required,
            has_param::YesVia::new(hint),
            name_type::Named::new(name),
        )
    }

    pub fn opt_multi_via<V: FromStr, T: From<V>, N: IntoName>(
        hint: &str,
        name: N,
    ) -> Arg<arity::Multiple, has_param::YesVia<V, T>, name_type::Named> {
        Arg::new(
            arity::Multiple,
            has_param::YesVia::new(hint),
            name_type::Named::new(name),
        )
    }

    pub fn flag<N: IntoName>(name: N) -> Arg<arity::Optional, has_param::No, name_type::Named> {
        Arg::new(arity::Optional, has_param::No, name_type::Named::new(name))
    }

    pub fn flag_count<N: IntoName>(
        name: N,
    ) -> Arg<arity::Multiple, has_param::No, name_type::Named> {
        Arg::new(arity::Multiple, has_param::No, name_type::Named::new(name))
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
            $crate::parser::Id::new(
                { $crate::args_all! {
                                        $a1, $($a),*
                                    } } .map(|($var1, $($var),*)| $b)
            )
        }
    };
}
