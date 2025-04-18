// TODO: better cli errors

macro_rules! opts {
    ($($name:ident),* $(,)?) => {
        #[derive(Clone, )]
        pub struct CodegenOpts {$(
            pub $name: bool,
        )*}

        impl CodegenOpts {
            #[must_use]
            pub fn all(bool: bool)  -> Self {
                Self { $($name: bool),* }
            }
            pub fn set_args<'a>(&mut self, args: impl IntoIterator<Item = &'a str>) {
                for arg in args {
                    let (arg, value) = arg.split_once('=').unwrap();
                    match arg.trim().to_ascii_lowercase().as_str() {
                        $(stringify!($name) => self.$name = parse_bool(value),)+
                        _ => panic!("invalid arg `{arg}`"),
                    }
                }
            }
        }
    };
}

fn parse_bool(s: &str) -> bool {
    match s.trim() {
        "0" | "false" => false,
        "1" | "true" => true,
        _ => panic!("invalid value `{s}`"),
    }
}

opts! {
    const_prop,
    not_branch,
    redundant_blocks,
    redundant_branch,
    fix_entry_block,
    remove_dead_assignments,
    remove_dead_places,
    remove_dead_blocks,
    remove_goto_terminator,
    remove_unreachable,

}
