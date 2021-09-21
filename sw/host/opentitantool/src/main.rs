// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use log::LevelFilter;
use structopt::StructOpt;

mod backend;
mod command;
use opentitanlib::app::command::CommandDispatch;

#[derive(Debug, StructOpt, CommandDispatch)]
enum RootCommandHierarchy {
    // Not flattened because `Bootstrap` is a leaf command.
    Bootstrap(command::bootstrap::BootstrapCommand),
    // Not flattened because `Console` is a leaf command.
    Console(command::console::Console),

    Gpio(command::gpio::GpioCommand),
    Spi(command::spi::SpiCommand),

    // Flattened because `Greetings` is a subcommand hierarchy.
    #[cfg(feature = "demo_commands")]
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
    env_logger::Builder::from_default_env()
        .filter(None, opts.logging)
        .init();

    let mut interface = backend::create(&opts.backend_opts)?;

    if let Some(value) = opts.command.run(&opts, &mut *interface)? {
        println!("{}", serde_json::to_string_pretty(&value)?);
    }
    Ok(())
}
