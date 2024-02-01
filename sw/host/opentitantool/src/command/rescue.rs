// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use opentitanlib::io::uart::UartParams;
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::rescue::boot_svc::{BootDataSlot, NextBootBl0};
use opentitanlib::rescue::serial::RescueSerial;

#[derive(Debug, serde::Serialize, Annotate)]
pub struct RawBytes(
    #[serde(with = "serde_bytes")]
    #[annotate(format=hexdump)]
    Vec<u8>,
);

#[derive(Debug, Args)]
pub struct Firmware {
    #[command(flatten)]
    params: UartParams,
    #[arg(value_name = "FILE")]
    filename: PathBuf,
}

impl CommandDispatch for Firmware {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let payload = std::fs::read(&self.filename)?;
        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport)?;
        rescue.update_firmware(payload.as_slice())?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct GetBootLog {
    #[command(flatten)]
    params: UartParams,
    #[arg(long, short, default_value = "false")]
    raw: bool,
}

impl CommandDispatch for GetBootLog {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport)?;
        if self.raw {
            let data = rescue.get_boot_log_raw()?;
            Ok(Some(Box::new(RawBytes(data))))
        } else {
            let data = rescue.get_boot_log()?;
            Ok(Some(Box::new(data)))
        }
    }
}

#[derive(Debug, Args)]
pub struct GetBootSvc {
    #[command(flatten)]
    params: UartParams,
    #[arg(long, short, default_value = "false")]
    raw: bool,
}

impl CommandDispatch for GetBootSvc {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport)?;
        if self.raw {
            let data = rescue.get_boot_svc_raw()?;
            Ok(Some(Box::new(RawBytes(data))))
        } else {
            let data = rescue.get_boot_svc()?;
            Ok(Some(Box::new(data)))
        }
    }
}

#[derive(Debug, Args)]
pub struct SetNextBl0Slot {
    #[command(flatten)]
    params: UartParams,
    #[arg(default_value = "SlotA")]
    slot: NextBootBl0,
}

impl CommandDispatch for SetNextBl0Slot {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport)?;
        rescue.set_next_bl0_slot(self.slot)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct SetPrimaryBl0Slot {
    #[command(flatten)]
    params: UartParams,
    #[arg(default_value = "SlotA")]
    slot: BootDataSlot,
}

impl CommandDispatch for SetPrimaryBl0Slot {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport)?;
        rescue.set_primary_bl0_slot(self.slot)?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum BootSvc {
    Get(GetBootSvc),
    SetNextBl0Slot(SetNextBl0Slot),
    SetPrimaryBl0Slot(SetPrimaryBl0Slot),
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum RescueCommand {
    #[command(subcommand)]
    BootSvc(BootSvc),
    GetBootLog(GetBootLog),
    Firmware(Firmware),
}
