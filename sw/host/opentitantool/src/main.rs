extern crate env_logger;
extern crate log;
extern crate opentitanlib;
extern crate opentitantool_derive;
extern crate serde;
extern crate serde_json;
extern crate structopt;

use anyhow::Result;
use log::LevelFilter;
use structopt::StructOpt;

mod backend;
mod command;
use command::CommandDispatch;

#[derive(Debug, StructOpt, CommandDispatch)]
enum RootCommandHierarchy {
    // Not flattened because `Console` is a leaf command.
    Console(command::console::Console),

    // Flattened because `Greetings` is a subcommand hierarchy.
    #[structopt(flatten)]
    Greetings(command::hello::Greetings),
}

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(long, default_value = "off")]
    logging: LevelFilter,

    #[structopt(flatten)]
    backend_opts: backend::BackendOpts,

    #[structopt(subcommand)]
    command: RootCommandHierarchy,
}

fn main() -> Result<()> {
    let opts = Opts::from_args();

    let mut builder = env_logger::Builder::from_default_env();
    builder.filter(None, opts.logging).init();

    let mut interface = backend::create(&opts.backend_opts)?;

    if let Some(value) = opts.command.run(&mut *interface)? {
        println!("{}", serde_json::to_string_pretty(&value)?);
    }
    Ok(())
}
