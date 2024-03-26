// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use clap::{Args, Subcommand};
use opentitanlib::io::uart::UartParams;
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::File;
use std::path::PathBuf;
use std::rc::Rc;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_svc::BootSlot;
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
use opentitanlib::image::image::Image;
use opentitanlib::image::manifest::ManifestKind;
use opentitanlib::rescue::serial::RescueSerial;
use opentitanlib::util::file::FromReader;
use opentitanlib::util::parse_int::ParseInt;

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
    #[arg(long, help = "After connecting to rescue, negotiate faster baudrate")]
    rate: Option<u32>,
    #[arg(long, default_value = "SlotA", help = "Which flash slot to rescue")]
    slot: BootSlot,
    #[arg(long, value_parser = usize::from_str, help = "Offset of application image")]
    offset: Option<usize>,
    #[arg(long, default_value_t = false, help = "Upload the file contents as-is")]
    raw: bool,
    #[arg(
        long,
        default_value_t = false,
        help = "Wait after upload (no automatic reboot)"
    )]
    wait: bool,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Reset the target to enter rescue mode"
    )]
    reset_target: bool,
    #[arg(value_name = "FILE")]
    filename: PathBuf,
}

impl CommandDispatch for Firmware {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = Image::read_from_file(&self.filename)?;
        let payload = if self.raw {
            image.bytes()
        } else {
            let subimages = image.subimages()?;
            let subimage = subimages
                .iter()
                .find(|s| {
                    s.kind == ManifestKind::Application
                        && (self.offset.is_none() || Some(s.offset) == self.offset)
                })
                .ok_or_else(|| anyhow!("No application image in {:?}", self.filename))?;
            log::info!("Found application image at offset {:#x}", subimage.offset);
            if self.slot != BootSlot::SlotA && self.offset.is_none() {
                log::warn!("Rescuing to {} may produce unexpected results.  Use `--offset` to select the desired application image.", self.slot);
            }
            subimage.data
        };
        let uart = self.params.create(transport)?;
        let mut prev_baudrate = 0u32;
        let rescue = RescueSerial::new(Rc::clone(&uart));
        rescue.enter(transport, self.reset_target)?;
        if let Some(rate) = self.rate {
            prev_baudrate = uart.get_baudrate()?;
            rescue.set_baud(rate)?;
        }
        if self.wait {
            rescue.wait()?;
        }
        rescue.update_firmware(self.slot, payload)?;
        if self.rate.is_some() {
            if self.wait {
                rescue.set_baud(prev_baudrate)?;
            } else {
                uart.set_baudrate(prev_baudrate)?;
            }
        }
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct GetBootLog {
    #[command(flatten)]
    params: UartParams,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Reset the target to enter rescue mode"
    )]
    reset_target: bool,
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
        rescue.enter(transport, self.reset_target)?;
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
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Reset the target to enter rescue mode"
    )]
    reset_target: bool,
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
        rescue.enter(transport, self.reset_target)?;
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
    #[arg(
        long,
        short,
        default_value = "Unspecified",
        help = "Set the primary boot slot"
    )]
    primary: BootSlot,
    #[arg(
        long,
        short,
        default_value = "Unspecified",
        help = "Set the one-time next boot slot"
    )]
    next: BootSlot,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Reset the target to enter rescue mode"
    )]
    reset_target: bool,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Get the response from the target"
    )]
    get_response: bool,
}

impl CommandDispatch for SetNextBl0Slot {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let uart = self.params.create(transport)?;
        let rescue = RescueSerial::new(uart);
        rescue.enter(transport, self.reset_target)?;
        rescue.set_next_bl0_slot(self.primary, self.next)?;
        if self.get_response {
            rescue.enter(transport, false)?;
            let response = rescue.get_boot_svc()?;
            rescue.reboot()?;
            Ok(Some(Box::new(response)))
        } else {
            Ok(None)
        }
    }
}

#[derive(Debug, Args)]
pub struct OwnershipUnlock {
    #[command(flatten)]
    params: UartParams,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Reset the target to enter rescue mode"
    )]
    reset_target: bool,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Get the response from the target"
    )]
    get_response: bool,
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
        rescue.enter(transport, self.reset_target)?;
        rescue.ownership_unlock(unlock)?;
        if self.get_response {
            rescue.enter(transport, false)?;
            let response = rescue.get_boot_svc()?;
            rescue.reboot()?;
            Ok(Some(Box::new(response)))
        } else {
            Ok(None)
        }
    }
}

#[derive(Debug, Args)]
pub struct OwnershipActivate {
    #[command(flatten)]
    params: UartParams,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Reset the target to enter rescue mode"
    )]
    reset_target: bool,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Get the response from the target"
    )]
    get_response: bool,
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
        rescue.enter(transport, self.reset_target)?;
        rescue.ownership_activate(activate)?;
        if self.get_response {
            rescue.enter(transport, false)?;
            let response = rescue.get_boot_svc()?;
            rescue.reboot()?;
            Ok(Some(Box::new(response)))
        } else {
            Ok(None)
        }
    }
}

#[derive(Debug, Args)]
pub struct SetOwnerConfig {
    #[command(flatten)]
    params: UartParams,
    #[arg(
        long,
        default_value_t = true,
        action = clap::ArgAction::Set,
        help = "Reset the target to enter rescue mode"
    )]
    reset_target: bool,
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
        rescue.enter(transport, self.reset_target)?;
        rescue.set_owner_config(&data)?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum BootSvcCommand {
    Get(GetBootSvc),
    SetNextBl0Slot(SetNextBl0Slot),
    OwnershipUnlock(OwnershipUnlock),
    OwnershipActivate(OwnershipActivate),
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum RescueCommand {
    #[command(subcommand)]
    BootSvc(BootSvcCommand),
    GetBootLog(GetBootLog),
    Firmware(Firmware),
    SetOwnerConfig(SetOwnerConfig),
}
