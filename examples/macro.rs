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
enum Colour {
    Red,
    Green,
    Blue,
}

#[derive(Debug)]
struct Args {
    int: i32,
    string: String,
    durations: Vec<Duration>,
    flag: bool,
    flag_count: usize,
    colour: Colour,
}

impl Args {
    fn parse() -> Self {
        (meap::let_map! {
            let {
                int = opt_opt("INT", 'i').with_default(42).name("int");
                string = pos_req("STRING").desc("a string");
                durations = pos_multi_via::<ParsableDuration, Duration>("DURATION");
                flag = flag('f').name("flag-with-a-really-long-name").desc("flag with a really long name");
                flag_count = flag_count('c');
                colour = meap::choose_at_most_one!(
                    flag("red").some_if(Colour::Red),
                    flag("green").some_if(Colour::Green),
                    flag("blue").some_if(Colour::Blue),
                ).with_general_default(Colour::Red);
            } in {
                Self {
                    int,
                    string,
                    durations,
                    flag,
                    flag_count,
                    colour,
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
