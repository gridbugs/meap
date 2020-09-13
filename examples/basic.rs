fn main() {
    use args_af::prelude::*;
    let (foo, verbosity): (String, _) = opt_req()
        .long("foo")
        .both(flag_count().short('v').long("verbose"))
        .parse_env()
        .unwrap();
    println!("{} {}", foo, verbosity);
}
