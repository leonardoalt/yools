use std::env;

use yools::symbolic::SymbolicArgs;
use yools::symbolic::Cmd;

use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[clap(name = "yools", version = env!("CARGO_PKG_VERSION"))]
struct Opts {
   #[clap(subcommand)]
   pub sub: Subcommands,
}

#[derive(Debug, Subcommand)]
#[clap(about = "Tools for Yul.")]
pub enum Subcommands {
    #[clap(about = "Symbolically execute Yul programs checking for reachability of solc panics")]
    Symbolic(SymbolicArgs),   
}


fn main() -> Result<(), String> {
    let opts = Opts::parse();
    match opts.sub {
        Subcommands::Symbolic(cmd) => {
            cmd.run()?;
        }
    }
    Ok(())
}
