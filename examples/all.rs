fn main() {
    let args = meap::all! {
        opt_opt::<u32, _>("A", 'a'),
        flag('b'),
        pos_req::<String>("FOO"),
        pos_req::<String>("BAR"),
        pos_multi::<String>("BAZ"),
        extra("ARGS").desc("arguments to pass to other program"),
    }
    .with_help_default()
    .with_program_description("example program")
    .with_version_default(env!("CARGO_PKG_VERSION"))
    .with_version_description("example version description")
    .parse_env_or_exit();
    println!("{:?}", args);
}
