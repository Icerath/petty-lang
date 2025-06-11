use std::path::PathBuf;

use clap::Parser;

use crate::CodegenOpts;

#[derive(Parser)]
struct CliArgs {
    command: Command,
    path: PathBuf,
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
    #[arg(short = 'x', long, help = "Turns off all optimizations unless overriden")]
    no_default_optimizations: bool,
    #[arg(long, action = clap::ArgAction::Set, default_value = "true", help = "Dumps the ast/hir/mir to the target directory ")]
    dump: bool,
    #[arg(long, default_value = "false")]
    show_auto: bool,
    #[arg(long, default_value = "target", help = "The target directory")]
    target: PathBuf,
    #[arg(short='C', long, action = clap::ArgAction::Append)]
    codegen: Vec<String>,
}

pub struct Args {
    pub command: Command,
    pub path: PathBuf,
    pub verbose: u8,
    pub dump: Option<PathBuf>,
    pub show_auto: bool,
    pub codegen: CodegenOpts,
}

impl Args {
    #[must_use]
    pub fn parse() -> Self {
        Self::from_cli(CliArgs::parse())
    }
    fn from_cli(args: CliArgs) -> Self {
        let mut opts = CodegenOpts::all(!args.no_default_optimizations);
        opts.set_args(args.codegen.iter().map(String::as_str));
        Self {
            command: args.command,
            path: args.path,
            verbose: args.verbose,
            show_auto: args.show_auto,
            dump: args.dump.then_some(args.target),
            codegen: opts,
        }
    }
}

#[derive(clap::ValueEnum, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Command {
    #[value(alias = "b")]
    Build,
    #[value(alias = "r")]
    Run,
}
