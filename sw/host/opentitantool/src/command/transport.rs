// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use regex::Regex;
use serde_annotate::Annotate;
use std::any::Any;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::transport::verilator::transport::Watch;

/// Initialize state of a transport debugger device to fit the device under test.  This
/// typically involves setting pins as input/output, open drain, etc. according to configuration
/// files.
#[derive(Debug, StructOpt)]
pub struct TransportInit {}

impl CommandDispatch for TransportInit {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Configure all GPIO pins to default direction and level, according to
        // configuration files provided.
        transport.apply_default_pin_configurations()?;
        Ok(None)
    }
}

/// Watch verilator's stdout for a regex or until a timeout is reached.
#[derive(Debug, StructOpt)]
pub struct VerilatorWatch {
    #[structopt(help = "Regular expresion to watch for")]
    regex: String,
    #[structopt(
        short,
        long, parse(try_from_str=humantime::parse_duration),
        help = "Duration to watch for the expresion",
    )]
    timeout: Option<Duration>,
}

impl CommandDispatch for VerilatorWatch {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let watch = Watch {
            regex: Regex::new(&self.regex)?,
            timeout: self.timeout,
        };
        transport.dispatch(&watch)
    }
}

/// Commands for interacting with the transport debugger device itself.
#[derive(Debug, StructOpt, CommandDispatch)]
pub enum TransportCommand {
    Init(TransportInit),
    VerilatorWatch(VerilatorWatch),
}
