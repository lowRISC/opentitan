// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use directories::ProjectDirs;
use log::LevelFilter;
use std::env::{args_os, ArgsOs};
use std::ffi::OsString;
use std::io::ErrorKind;
use std::iter::{IntoIterator, Iterator};
use std::path::PathBuf;
use structopt::StructOpt;

use opentitanlib::backend;
use opentitanlib::proxy::SessionHandler;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "opentitansession",
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

    #[structopt(flatten)]
    backend_opts: backend::BackendOpts,

    #[structopt(long)]
    listen_port: Option<u16>,

    #[structopt(long, help = "Start session, staying in foreground (do not daemonize)")]
    debug: bool,
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

    if opts.debug {
        // Start session process in foreground (do not daemonize)
        let transport = backend::create(&opts.backend_opts, "null")?;
        let mut session = SessionHandler::init(&transport, opts.listen_port)?;
        println!("Listening on port {}", session.get_port());
        session.run_loop()?;
        return Ok(());
    }

    unimplemented!("Background daemon not implemented");
}
