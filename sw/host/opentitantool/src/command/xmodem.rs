// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use opentitanlib::io::uart::UartParams;
use serde_annotate::Annotate;
use std::any::Any;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::rescue::xmodem::Xmodem;

#[derive(Debug, Args)]
pub struct XmodemSend {
    #[command(flatten)]
    params: UartParams,
    #[arg(value_name = "FILE")]
    filename: String,
}

impl CommandDispatch for XmodemSend {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let payload = std::fs::read(&self.filename)?;
        let xmodem = Xmodem::new();
        let uart = self.params.create(transport)?;
        uart.clear_rx_buffer()?;
        xmodem.send(&*uart, payload.as_slice())?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct XmodemRecv {
    #[command(flatten)]
    params: UartParams,
    #[arg(value_name = "FILE")]
    filename: String,
}

impl CommandDispatch for XmodemRecv {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let uart = self.params.create(transport)?;
        uart.clear_rx_buffer()?;
        let xmodem = Xmodem::new();
        let mut data = Vec::new();
        xmodem.receive(&*uart, &mut data)?;
        std::fs::write(&self.filename, &data)?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum XmodemCommand {
    Send(XmodemSend),
    Recv(XmodemRecv),
}
