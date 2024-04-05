// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use regex::Regex;
use serde_annotate::Annotate;
use std::any::Any;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::{StagedProgressBar, TransportWrapper};
use opentitanlib::transport::verilator::transport::Watch;
use opentitanlib::transport::UpdateFirmware;

/// Initialize state of a transport debugger device to fit the device under test.  This
/// typically involves setting pins as input/output, open drain, etc. according to configuration
/// files.
#[derive(Debug, Args)]
pub struct TransportInit {
    /// Optional gpio strap to apply during transport initialization.
    #[arg(short, long)]
    pub gpio_strap: Option<String>,
}

impl CommandDispatch for TransportInit {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Configure all GPIO pins to default direction and level, according to
        // configuration files provided, and configures SPI port mode/speed, etc.
        // Also apply an optional, named gpio strap while performing pin initialization.
        transport.apply_default_configuration(self.gpio_strap.as_deref())?;
        Ok(None)
    }
}

/// Updates the firmware of the debugger/transport.  If no argument is given, a suitable
/// "official" firmware will be used, if one such was compiled into the OpenTitanTool binary.  For
/// instructions on how to build HyperDebug firmware locally, see
/// https://docs.google.com/document/d/1ZEH7L5j9-wMw4tkW28-xt6JU5B6hTX0RdZD4h4OZzDo .
#[derive(Debug, Args)]
pub struct TransportUpdateFirmware {
    /// Local firmware file to use instead of official release.
    #[arg(short, long)]
    filename: Option<PathBuf>,

    /// Update even if transport already reports identical version number.
    #[arg(long)]
    force: bool,
}

impl CommandDispatch for TransportUpdateFirmware {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let firmware = match self.filename.as_ref() {
            Some(name) => Some(fs::read(name)?),
            None => None,
        };
        let progress = StagedProgressBar::new();
        let operation = UpdateFirmware {
            firmware,
            progress: Box::new(progress),
            force: self.force,
        };
        transport.dispatch(&operation)
    }
}

/// Watch verilator's stdout for a regex or until a timeout is reached.
#[derive(Debug, Args)]
pub struct VerilatorWatch {
    /// Regular expresion to watch for.
    regex: String,
    /// Duration to watch for the expresion.
    #[arg(short, long, value_parser=humantime::parse_duration)]
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

#[derive(Debug, Args)]
pub struct TransportQuery {
    /// User defined key to look up.
    key: String,
}

#[derive(serde::Serialize)]
pub struct TransportQueryResult {
    key: String,
    value: String,
}

impl CommandDispatch for TransportQuery {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let value = transport.query_provides(&self.key)?;
        Ok(Some(Box::new(TransportQueryResult {
            key: self.key.clone(),
            value: value.to_string(),
        })))
    }
}

#[derive(Debug, Args)]
pub struct TransportQueryAll {}

impl CommandDispatch for TransportQueryAll {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let value: HashMap<String, String> = transport.provides_map()?.clone();
        Ok(Some(Box::new(value)))
    }
}

/// Commands for interacting with the transport debugger device itself.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum TransportCommand {
    Init(TransportInit),
    VerilatorWatch(VerilatorWatch),
    UpdateFirmware(TransportUpdateFirmware),
    Query(TransportQuery),
    QueryAll(TransportQueryAll),
}
