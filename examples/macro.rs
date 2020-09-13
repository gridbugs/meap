use std::str::FromStr;
use std::time::Duration;

#[derive(Debug)]
struct ParsableDuration(Duration);

impl FromStr for ParsableDuration {
    type Err = parse_duration::parse::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_duration::parse(s).map(ParsableDuration)
    }
}

impl From<ParsableDuration> for Duration {
    fn from(d: ParsableDuration) -> Self {
        d.0
    }
}

#[derive(Debug)]
struct Args {
    optional_int: Option<i32>,
    string: String,
    durations: Vec<Duration>,
    flag: bool,
    flag_count: usize,
}

impl Args {
    fn parse() -> Self {
        (args_af::args_map! {
            let {
                optional_int = opt_opt().s('i');
                string = opt_req().s('s');
                durations = opt_multi_via::<ParsableDuration, Duration>();
                flag = flag().s('f');
                flag_count = flag_count().s('c');
            } in {
                Self {
                    optional_int,
                    string,
                    durations,
                    flag,
                    flag_count,
                }
            }
        })
        .parse_env()
        .unwrap()
    }
}

fn main() {
    println!("{:#?}", Args::parse());
}
