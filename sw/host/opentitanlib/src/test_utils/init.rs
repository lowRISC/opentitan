// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use directories::ProjectDirs;
use log::LevelFilter;
use serde_annotate::Annotate;
use std::env::ArgsOs;
use std::ffi::OsString;
use std::io::ErrorKind;
use std::iter::Iterator;
use std::path::PathBuf;
use structopt::StructOpt;

use super::bootstrap::Bootstrap;
use super::load_bitstream::LoadBitstream;
use crate::app::TransportWrapper;
use crate::backend;
// use opentitanlib::io::uart::UartParams;

#[derive(Debug, StructOpt)]
pub struct InitializeTest {
    #[structopt(
        long,
        default_value = "config",
        help = "Filename of a default flagsfile.  Relative to $XDG_CONFIG_HOME/opentitantool."
    )]
    pub rcfile: PathBuf,

    #[structopt(long, default_value = "off")]
    pub logging: LevelFilter,

    #[structopt(flatten)]
    pub backend_opts: backend::BackendOpts,

    // TODO: Bootstrap::options already has a uart_params (and a spi_params).
    // This probably needs some refactoring.
    //#[structopt(flatten)]
    //pub uart_params: UartParams,
    #[structopt(flatten)]
    pub load_bitstream: LoadBitstream,

    #[structopt(flatten)]
    pub bootstrap: Bootstrap,
}

impl InitializeTest {
    pub fn init_logging(&self) {
        let level = self.logging;
        // The tests might use OpenOCD which uses util::printer so we will get
        // more useful logging if we log the target instead of the module path
        if level != LevelFilter::Off {
            env_logger::Builder::from_default_env()
                .format_target(true)
                .format_module_path(false)
                .filter(None, level)
                .init();
        }
    }

    // Given some existing option configuration, maybe re-evaluate command
    // line options by reading an `rcfile`.
    pub fn parse_command_line(&self, mut args: ArgsOs) -> Result<Vec<OsString>> {
        // Initialize the logger if the user requested the non-defualt option.
        self.init_logging();
        if self.rcfile.as_os_str().is_empty() {
            // No rcfile to parse.
            return Ok(Vec::new());
        }

        // Construct the rcfile path based on the user's config directory
        // (ie: $HOME/.config/opentitantool/<filename>).
        let rcfile = if let Some(base) = ProjectDirs::from("org", "opentitan", "opentitantool") {
            base.config_dir().join(&self.rcfile)
        } else {
            self.rcfile.clone()
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
        Ok(arguments)
    }

    // Print the result of a command.
    // If there is an error and `RUST_BACKTRACE=1`, print a backtrace.
    pub fn print_result(operation: &str, result: Result<Option<Box<dyn Annotate>>>) -> Result<()> {
        match result {
            Ok(Some(value)) => {
                log::info!("{}: success.", operation);
                println!(
                    "\"{}\": {}",
                    operation,
                    serde_json::to_string_pretty(&value)?
                );
                Ok(())
            }
            Ok(None) => {
                log::info!("{}: success.", operation);
                println!("\"{}\": true", operation);
                Ok(())
            }
            Err(e) => {
                log::info!("{}: {:?}.", operation, e);
                println!("\"{}\": false", operation);
                Err(e)
            }
        }
    }

    pub fn init_target(&self) -> Result<TransportWrapper> {
        // Create the transport interface.
        let transport = backend::create(&self.backend_opts)?;

        // Set up the default pin configurations as specified in the transport's config file.
        transport.apply_default_configuration()?;

        // Create the UART first to initialize the desired parameters.
        let _uart = self.bootstrap.options.uart_params.create(&transport)?;

        // Bootstrap an rv32 test program.
        Self::print_result("bootstrap", self.bootstrap.init(&transport))?;
        Ok(transport)
    }
}
