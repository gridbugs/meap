fn main() {
    let (a, b, c) = meap::all! {
        opt_opt::<u32, _>("A", 'a'),
        flag('b'),
        pos_req::<String>("FOO"),
    }
    .with_help_default()
    .with_program_description("example program")
    .parse_env_or_exit();
    println!("{:?} {:?} {:?}", a, b, c);
}
