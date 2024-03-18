// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use opentitanlib::io::uart::UartParams;
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::File;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_svc::{BootDataSlot, NextBootBl0};
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
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

#[derive(Debug, Args)]
pub struct OwnershipUnlock {
    #[command(flatten)]
    params: UartParams,
    #[command(flatten)]
    unlock: OwnershipUnlockParams,
    #[arg(short, long, help = "A file containing a binary unlock request")]
    input: Option<PathBuf>,
}

impl CommandDispatch for OwnershipUnlock {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let unlock = self
            .unlock
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;

        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport)?;
        rescue.ownership_unlock(unlock)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct OwnershipActivate {
    #[command(flatten)]
    params: UartParams,
    #[command(flatten)]
    activate: OwnershipActivateParams,
    #[arg(short, long, help = "A file containing a binary activate request")]
    input: Option<PathBuf>,
}

impl CommandDispatch for OwnershipActivate {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let activate = self
            .activate
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;

        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport)?;
        rescue.ownership_activate(activate)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct SetOwnerConfig {
    #[command(flatten)]
    params: UartParams,
    #[arg(help = "A signed owner configuration block")]
    input: PathBuf,
}

impl CommandDispatch for SetOwnerConfig {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let data = std::fs::read(&self.input)?;
        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport)?;
        rescue.set_owner_config(&data)?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum BootSvc {
    Get(GetBootSvc),
    SetNextBl0Slot(SetNextBl0Slot),
    SetPrimaryBl0Slot(SetPrimaryBl0Slot),
    OwnershipUnlock(OwnershipUnlock),
    OwnershipActivate(OwnershipActivate),
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum RescueCommand {
    #[command(subcommand)]
    BootSvc(BootSvc),
    GetBootLog(GetBootLog),
    Firmware(Firmware),
    SetOwnerConfig(SetOwnerConfig),
}
