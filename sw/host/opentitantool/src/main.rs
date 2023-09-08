// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![feature(min_specialization)]
use anyhow::Result;
use clap::{Parser, ValueEnum};
use directories::ProjectDirs;
use log::LevelFilter;
use serde_annotate::Annotate;
use serde_annotate::ColorProfile;
use std::env::{args_os, ArgsOs};
use std::ffi::OsString;
use std::io::ErrorKind;
use std::io::IsTerminal;
use std::iter::{IntoIterator, Iterator};
use std::path::PathBuf;
use std::str::FromStr;

mod command;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::backend;

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Parser, CommandDispatch)]
enum RootCommandHierarchy {
    // Not flattened because `Bootstrap` is a leaf command.
    Bootstrap(command::bootstrap::BootstrapCommand),
    // Not flattened because `Console` is a leaf command.
    Console(command::console::Console),

    #[command(subcommand)]
    Gpio(command::gpio::GpioCommand),
    #[command(subcommand)]
    Emulator(command::emulator::EmuCommand),

    #[command(subcommand)]
    Fpga(command::fpga::FpgaCommand),
    I2c(command::i2c::I2cCommand),
    #[command(subcommand)]
    Image(command::image::Image),
    NoOp(command::NoOp),
    #[command(subcommand)]
    Otp(command::otp::Otp),
    #[command(subcommand)]
    Rsa(command::rsa::Rsa),
    Spi(command::spi::SpiCommand),
    #[command(subcommand)]
    Spx(command::spx::Spx),
    #[command(subcommand)]
    Transport(command::transport::TransportCommand),
    Version(command::version::Version),
    #[command(subcommand)]
    Status(command::status_cmd::StatusCommand),

    // Flattened because `Greetings` is a subcommand hierarchy.
    #[cfg(feature = "demo_commands")]
    #[command(subcommand)]
    Greetings(command::hello::Greetings),
}

#[derive(Clone, Copy, Debug, ValueEnum)]
#[value(rename_all = "verbatim")]
enum Format {
    Json,
    Json5,
    HJson,
    Yaml,
}

#[derive(Debug, Parser)]
#[command(
    name = "opentitantool",
    about = "A tool for interacting with OpenTitan chips."
)]
struct Opts {
    /// Filename of a default flagsfile.  Relative to $XDG_CONFIG_HOME/opentitantool.
    #[arg(long, value_parser = PathBuf::from_str, default_value = "config")]
    rcfile: PathBuf,

    #[arg(long, default_value = "warn")]
    logging: LevelFilter,

    /// Preferred output format.
    #[arg(short, long, value_enum, ignore_case = true, default_value = "hjson")]
    format: Format,

    /// Use color in the output.
    #[arg(short, long, value_parser = bool::from_str)]
    color: Option<bool>,

    /// Do not print command results.
    #[arg(short, long)]
    quiet: bool,

    /// Parse and execute the argument as a command.
    #[arg(long, num_args = 1)]
    exec: Vec<String>,

    #[command(flatten)]
    backend_opts: backend::BackendOpts,

    #[command(subcommand)]
    command: RootCommandHierarchy,
}

// Given some existing option configuration, maybe re-evaluate command
// line options by reading an `rcfile`.
fn parse_command_line(opts: Opts, mut args: ArgsOs) -> Result<Opts> {
    // Initialize the logger if the user requested the non-defualt option.
    let logging = opts.logging;
    if logging != LevelFilter::Off {
        env_logger::Builder::from_default_env()
            .format_target(true)
            .format_module_path(false)
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
    arguments.extend(args);
    let opts = Opts::parse_from(&arguments);
    if opts.logging != logging {
        // Try re-initializing the logger.  Ignore errors.
        let _ = env_logger::Builder::from_default_env()
            .format_target(true)
            .format_module_path(false)
            .filter(None, opts.logging)
            .try_init();
    }
    Ok(opts)
}

// Print the result of a command.
// If there is an error and `RUST_BACKTRACE=1`, print a backtrace.
fn print_command_result(opts: &Opts, result: Result<Option<Box<dyn Annotate>>>) -> Result<()> {
    match result {
        Ok(Some(value)) => {
            log::info!("Command result: success.");
            if opts.quiet {
                return Ok(());
            }
            let profile = if std::io::stdout().is_terminal() && opts.color.unwrap_or(true) {
                ColorProfile::basic()
            } else {
                ColorProfile::default()
            };
            let doc = serde_annotate::serialize(value.as_ref())?;
            let string = match opts.format {
                Format::Json => doc.to_json().color(profile).to_string(),
                Format::Json5 => doc.to_json5().color(profile).to_string(),
                Format::HJson => doc.to_hjson().color(profile).to_string(),
                Format::Yaml => doc.to_yaml().color(profile).to_string(),
            };
            println!("{}", string);
            Ok(())
        }
        Ok(None) => {
            log::info!("Command result: success.");
            Ok(())
        }
        Err(e) => {
            log::info!("Command result: {:?}", e);
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
    let command = RootCommandHierarchy::parse_from(
        std::iter::once(OsString::from("opentitantool")).chain(args),
    );
    print_command_result(opts, command.run(opts, transport))?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = parse_command_line(Opts::parse(), args_os())?;

    let transport = backend::create(&opts.backend_opts)?;

    for command in &opts.exec {
        execute(
            shellwords::split(command)?.iter().map(OsString::from),
            &opts,
            &transport,
        )?;
    }
    print_command_result(&opts, opts.command.run(&opts, &transport))?;
    Ok(())
}
