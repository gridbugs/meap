fn main() {
    use meap::prelude::*;
    let (foo, verbosity): (String, _) = opt_req("STRING", "foo")
        .both(flag_count('v').name("verbose"))
        .with_help_default()
        .parse_env_or_exit();
    println!("{} {}", foo, verbosity);
}
