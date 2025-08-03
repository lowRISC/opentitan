// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::uart::UartParams;

/// Outputs `"/dev/ttyUSBn"` or similar OS device path usable by external programs for directly
/// accessing the given serial port of the debugger.
#[derive(Debug, Args)]
pub struct UartOsDevice {}

#[derive(Debug, serde::Serialize)]
pub struct UartOsDeviceResponse {
    path: String,
}

impl CommandDispatch for UartOsDevice {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let context = context.downcast_ref::<UartCommand>().unwrap();
        let uart = context.params.create(transport)?;
        Ok(Some(Box::new(UartOsDeviceResponse {
            path: uart.get_device_path()?,
        })))
    }
}

/// Commands for interacting with a UART.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum InternalUartCommand {
    OsDevice(UartOsDevice),
}

#[derive(Debug, Args)]
pub struct UartCommand {
    #[command(flatten)]
    params: UartParams,

    #[command(subcommand)]
    command: InternalUartCommand,
}

impl CommandDispatch for UartCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // None of the UART commands care about the prior context, but they do
        // care about the `UartParams` parameter in the current node.
        self.command.run(self, transport)
    }
}
