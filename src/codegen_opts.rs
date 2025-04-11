use clap::{Parser, arg};

macro_rules! opts {
    ($($name:ident),* $(,)?) => {
        #[derive(Clone, Parser)]
        pub struct CodegenOpts {$(
            #[arg(
                long=concat!("O", stringify!($name)),
                action=clap::ArgAction::Set,
                default_value="true",
                default_value_if("no_default_optimizations", "true", "false"),
                hide_possible_values=true,
                value_name="true|false",
            )]
            pub $name: bool,
        )*}

        impl Default for CodegenOpts {
            fn default() -> Self {
                Self { $($name: true),* }
            }
        }
    };
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
