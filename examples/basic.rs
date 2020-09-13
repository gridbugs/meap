fn main() {
    use meap::prelude::*;
    let (foo, verbosity): (String, _) = opt_req("foo")
        .both(flag_count('v').long("verbose"))
        .parse_env()
        .unwrap();
    println!("{} {}", foo, verbosity);
}
