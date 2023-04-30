#[derive(Debug)]
enum Foo {
    A(String),
    B(String),
}

struct Args {
    foo: Option<Foo>,
}

impl Args {
    fn parser() -> impl meap::Parser<Item = Self> {
        meap::let_map! {
            let {
                foo = meap::choose_at_most_one![
                    opt_opt("STRING", 'a').map_opt(Foo::A),
                    opt_opt("STRINg", 'b')
                        .map(|o| o.map(|s: String| format!("[{}]", s)))
                        .map_opt(Foo::B)
                        .map_opt(|x| x),
                ];
            } in {
                Self { foo }
            }
        }
    }
}

fn main() {
    use meap::Parser;
    let args = Args::parser().with_help_default().parse_env_or_exit();
    println!("{:?}", args.foo);
}
