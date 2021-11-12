// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use directories::ProjectDirs;
use log::LevelFilter;
use std::env::{args_os, ArgsOs};
use std::ffi::OsString;
use std::io::ErrorKind;
use std::path::PathBuf;
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
    Image(command::image::Image),
    LoadBitstream(command::load_bitstream::LoadBitstream),
    Spi(command::spi::SpiCommand),

    // Flattened because `Greetings` is a subcommand hierarchy.
    #[cfg(feature = "demo_commands")]
    #[structopt(flatten)]
    Greetings(command::hello::Greetings),
}

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(
        long,
        default_value = "config",
        help = "Filename of a default flagsfile.  Relative to $XDG_CONFIG_HOME/opentitantool."
    )]
    rcfile: PathBuf,

    #[structopt(long, default_value = "off")]
    logging: LevelFilter,

    #[structopt(flatten)]
    backend_opts: backend::BackendOpts,

    #[structopt(subcommand)]
    command: RootCommandHierarchy,
}

// Given some existing option configuration, maybe re-evaluate command
// line options by reading an `rcfile`.
fn parse_command_line(opts: Opts, mut args: ArgsOs) -> Result<Opts> {
    // Initialize the logger if the user requested the non-defualt option.
    let logging = opts.logging;
    if logging != LevelFilter::Off {
        env_logger::Builder::from_default_env()
            .filter(None, opts.logging)
            .init();
    }
    if opts.rcfile.as_os_str().is_empty() {
        // No rcfile to parse.
        return Ok(opts);
    }

    // Construct the rcfile path based on the user's config directory
    // (ie: $HOME/.config/opentitantool/<filename>).
    let rcfile = if let Some(base) = ProjectDirs::from("org", "opentitan", "opentitantool") {
        base.config_dir().join(&opts.rcfile)
    } else {
        opts.rcfile
    };

    // argument[0] is the executable name.
    let mut arguments = vec![args.next().unwrap()];

    // Read in the rcfile and extend the argument list.
    match std::fs::read_to_string(&rcfile) {
        Ok(content) => {
            for line in content.split('\n') {
                // Strip basic comments as shellwords won't handle comments.
                let (line, _) = line.split_once('#').unwrap_or((line, ""));
                arguments.extend(shellwords::split(line)?.iter().map(OsString::from));
            }
            Ok(())
        }
        Err(e) if e.kind() == ErrorKind::NotFound => {
            log::warn!("Could not read {:?}. Ignoring.", rcfile);
            Ok(())
        }
        Err(e) => Err(anyhow::Error::new(e).context(format!("Reading file {:?}", rcfile))),
    }?;

    // Extend the argument list with all remaining command line arguments.
    arguments.extend(args.into_iter());
    let opts = Opts::from_iter(&arguments);
    if opts.logging != logging {
        // Try re-initializing the logger.  Ignore errors.
        let _ = env_logger::Builder::from_default_env()
            .filter(None, opts.logging)
            .try_init();
    }
    Ok(opts)
}

fn main() -> Result<()> {
    let opts = parse_command_line(Opts::from_args(), args_os())?;

    let transport = backend::create(&opts.backend_opts)?;

    if let Some(value) = opts.command.run(&opts, &transport)? {
        println!("{}", serde_json::to_string_pretty(&value)?);
    }
    Ok(())
}
