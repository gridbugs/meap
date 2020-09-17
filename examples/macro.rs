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
        (meap::args_map! {
            let {
                optional_int = opt_opt("INT", 'i');
                string = pos_req("STRING").desc("a string");
                durations = pos_multi_via::<ParsableDuration, Duration>("DURATION");
                flag = flag('f').name("flag-with-a-really-long-name").desc("flag with a really long name");
                flag_count = flag_count('c');
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
        .with_help_default()
        .parse_env_or_exit()
    }
}

fn main() {
    let args = Args::parse();
    println!("{:?}", args);
}
