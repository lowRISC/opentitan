// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use directories::ProjectDirs;
use erased_serde::Serialize;
use log::LevelFilter;
use std::env::{args_os, ArgsOs};
use std::ffi::OsString;
use std::io::ErrorKind;
use std::iter::{IntoIterator, Iterator};
use std::path::PathBuf;
use structopt::StructOpt;

mod command;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::backend;

#[derive(Debug, StructOpt, CommandDispatch)]
enum RootCommandHierarchy {
    // Not flattened because `Bootstrap` is a leaf command.
    Bootstrap(command::bootstrap::BootstrapCommand),
    // Not flattened because `Console` is a leaf command.
    Console(command::console::Console),

    Gpio(command::gpio::GpioCommand),

    I2c(command::i2c::I2cCommand),
    Image(command::image::Image),
    LoadBitstream(command::load_bitstream::LoadBitstream),
    NoOp(command::NoOp),
    Spi(command::spi::SpiCommand),

    // Flattened because `Greetings` is a subcommand hierarchy.
    #[cfg(feature = "demo_commands")]
    #[structopt(flatten)]
    Greetings(command::hello::Greetings),
}

#[derive(Debug, StructOpt)]
#[structopt(
    name = "opentitantool",
    about = "A tool for interacting with OpenTitan chips."
)]
struct Opts {
    #[structopt(
        long,
        default_value = "config",
        help = "Filename of a default flagsfile.  Relative to $XDG_CONFIG_HOME/opentitantool."
    )]
    rcfile: PathBuf,

    #[structopt(long, default_value = "off")]
    logging: LevelFilter,

    #[structopt(
        long,
        number_of_values(1),
        help = "Parse and execute the argument as a command"
    )]
    exec: Vec<String>,

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

// Print the result of a command.
// If there is an error and `RUST_BACKTRACE=1` _and_ `--logging=debug`, print a backtrace.
fn print_command_result(result: Result<Option<Box<dyn Serialize>>>) -> Result<()> {
    match result {
        Ok(Some(value)) => {
            println!("{}", serde_json::to_string_pretty(&value)?);
            Ok(())
        }
        Ok(None) => Ok(()),
        Err(e) => {
            log::debug!("{:?}", e);
            Err(e)
        }
    }
}

// Execute is a convenience function for taking a list of strings,
// parsing them into a command, executing the command and printing the result.
fn execute<I>(args: I, opts: &Opts, transport: &TransportWrapper) -> Result<()>
where
    I: IntoIterator<Item = OsString>,
{
    let command = RootCommandHierarchy::from_iter(
        std::iter::once(OsString::from("opentitantool")).chain(args),
    );
    print_command_result(command.run(opts, &transport))?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = parse_command_line(Opts::from_args(), args_os())?;

    let transport = backend::create(&opts.backend_opts)?;

    for command in &opts.exec {
        execute(
            shellwords::split(command)?.iter().map(OsString::from),
            &opts,
            &transport,
        )?;
    }
    print_command_result(opts.command.run(&opts, &transport))?;
    Ok(())
}
