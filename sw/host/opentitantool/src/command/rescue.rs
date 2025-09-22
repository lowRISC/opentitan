// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::File;
use std::path::PathBuf;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::chip::boot_svc::BootSlot;
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
use opentitanlib::image::image::Image;
use opentitanlib::image::manifest::ManifestKind;
use opentitanlib::ownership::{OwnerBlock, TlvHeader};
use opentitanlib::rescue::{EntryMode, RescueMode, RescueParams};
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
    #[arg(long, help = "After connecting to rescue, negotiate faster baudrate")]
    rate: Option<u32>,
    #[arg(long, default_value = "SlotA", help = "Which flash slot to rescue")]
    slot: BootSlot,
    #[arg(long, value_parser = usize::from_str, help = "Offset of application image")]
    offset: Option<usize>,
    #[arg(long, default_value_t = false, help = "Upload the file contents as-is")]
    raw: bool,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(value_name = "FILE")]
    filename: PathBuf,
}

impl CommandDispatch for Firmware {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
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
                log::warn!(
                    "Rescuing to {} may produce unexpected results.  Use `--offset` to select the desired application image.",
                    self.slot
                );
            }
            subimage.data
        };
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        let mut prev_baudrate = 0u32;
        rescue.enter(transport, self.reset_target)?;
        if let Some(rate) = self.rate {
            prev_baudrate = rescue.set_speed(rate)?;
        }
        rescue.update_firmware(self.slot, payload)?;
        if self.rate.is_some() {
            rescue.set_speed(prev_baudrate)?;
        }
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct GetBootLog {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
    #[arg(long, short, default_value = "false")]
    raw: bool,
}

impl CommandDispatch for GetBootLog {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        let result: Box<dyn erased_serde::Serialize> = if self.raw {
            let data = rescue.get_raw(RescueMode::BootLog)?;
            Box::new(RawBytes(data))
        } else {
            let data = rescue.get_boot_log()?;
            Box::new(data)
        };
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(Some(result))
    }
}

#[derive(Debug, Args)]
pub struct GetBootSvc {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
    #[arg(long, short, default_value = "false")]
    raw: bool,
}

impl CommandDispatch for GetBootSvc {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        let result: Box<dyn erased_serde::Serialize> = if self.raw {
            let data = rescue.get_raw(RescueMode::BootSvcRsp)?;
            Box::new(RawBytes(data))
        } else {
            let data = rescue.get_boot_svc()?;
            Box::new(data)
        };
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(Some(result))
    }
}

#[derive(Debug, Args)]
pub struct GetDeviceId {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
    #[arg(long, short, default_value = "false")]
    raw: bool,
}

impl CommandDispatch for GetDeviceId {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        let result: Box<dyn erased_serde::Serialize> = if self.raw {
            let data = rescue.get_raw(RescueMode::DeviceId)?;
            Box::new(RawBytes(data))
        } else {
            let data = rescue.get_device_id()?;
            Box::new(data)
        };
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(Some(result))
    }
}

#[derive(Debug, Args)]
pub struct SetNextBl0Slot {
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
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
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
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        rescue.set_next_bl0_slot(self.primary, self.next)?;
        let result = if self.get_response {
            rescue.enter(transport, EntryMode::Reboot)?;
            let response = rescue.get_boot_svc()?;
            Some(Box::new(response) as Box<dyn erased_serde::Serialize>)
        } else {
            None
        };
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(result)
    }
}

#[derive(Debug, Args)]
pub struct OwnershipUnlock {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
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
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let (unlock, signature) = self
            .unlock
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;

        if self.unlock.algorithm.is_detached() && signature.is_some() {
            log::warn!(
                "The algorithm {} requires a detached signature, but rescue cannot deliver the detached signature as part of boot services.",
                self.unlock.algorithm
            );
        }
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        rescue.ownership_unlock(unlock)?;
        let result = if self.get_response {
            rescue.enter(transport, EntryMode::Reboot)?;
            let response = rescue.get_boot_svc()?;
            Some(Box::new(response) as Box<dyn erased_serde::Serialize>)
        } else {
            None
        };
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(result)
    }
}

#[derive(Debug, Args)]
pub struct OwnershipActivate {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
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
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let (activate, signature) = self
            .activate
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;

        if self.activate.algorithm.is_detached() && signature.is_some() {
            log::warn!(
                "The algorithm {} requires a detached signature, but rescue cannot deliver the detached signature as part of boot services.",
                self.activate.algorithm
            );
        }
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        rescue.ownership_activate(activate)?;
        let result = if self.get_response {
            rescue.enter(transport, EntryMode::Reboot)?;
            let response = rescue.get_boot_svc()?;
            Some(Box::new(response) as Box<dyn erased_serde::Serialize>)
        } else {
            None
        };
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(result)
    }
}

#[derive(Debug, Args)]
pub struct SetOwnerConfig {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
    #[arg(help = "A signed owner configuration block")]
    input: PathBuf,
}

impl CommandDispatch for SetOwnerConfig {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let data = std::fs::read(&self.input)?;
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        rescue.set_owner_config(&data)?;
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct GetOwnerConfig {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
    #[arg(long, short, default_value = "false", conflicts_with = "output")]
    raw: bool,
    #[arg(long, short, default_value = "0", help = "Owner page number")]
    page: u32,
    #[arg(
        short,
        long,
        conflicts_with = "raw",
        help = "Write the binary form to a file"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for GetOwnerConfig {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let page = match self.page {
            0 => RescueMode::GetOwnerPage0,
            1 => RescueMode::GetOwnerPage1,
            _ => return Err(anyhow!("Unsupported page {}", self.page)),
        };
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        let data = rescue.get_raw(page)?;
        let result = if let Some(output) = &self.output {
            std::fs::write(output, &data)?;
            None
        } else if self.raw {
            Some(Box::new(RawBytes(data)) as Box<dyn erased_serde::Serialize>)
        } else {
            let mut cursor = std::io::Cursor::new(&data);
            let header = TlvHeader::read(&mut cursor)?;
            Some(Box::new(OwnerBlock::read(&mut cursor, header)?)
                as Box<dyn erased_serde::Serialize>)
        };
        if self.reboot {
            rescue.reboot()?;
        }
        Ok(result)
    }
}

#[derive(Debug, Args)]
/// Rescue No-op.
pub struct NoOp {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
}

impl CommandDispatch for NoOp {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<RescueCommand>().unwrap();
        let rescue = context.params.create(transport)?;
        rescue.enter(transport, self.reset_target)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct EraseOwner {
    #[arg(
        long,
        value_enum,
        default_value_t = EntryMode::Reset,
        help = "Method to reset for rescue mode",
    )]
    reset_target: EntryMode,
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Reboot after the rescue command")]
    reboot: bool,
    #[arg(long, default_value_t = false, help = "Really erase the owner config")]
    really: bool,
}

impl CommandDispatch for EraseOwner {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        if self.really {
            let context = context.downcast_ref::<RescueCommand>().unwrap();
            let rescue = context.params.create(transport)?;
            rescue.enter(transport, self.reset_target)?;
            rescue.erase_owner()?;
            if self.reboot {
                rescue.reboot()?;
            }
            Ok(None)
        } else {
            Err(anyhow!(
                "The owner may only be erased on DEV lifecycle-state chips with a ROM_EXT configured to permit owner erasing.\n\nUse the `--really` flag to send the command."
            ))
        }
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
pub enum InternalRescueCommand {
    #[command(subcommand)]
    BootSvc(BootSvcCommand),
    EraseOwner(EraseOwner),
    GetBootLog(GetBootLog),
    GetDeviceId(GetDeviceId),
    Firmware(Firmware),
    SetOwnerConfig(SetOwnerConfig),
    GetOwnerConfig(GetOwnerConfig),
    NoOp(NoOp),
}

#[derive(Debug, Args)]
pub struct RescueCommand {
    #[command(flatten)]
    params: RescueParams,

    #[command(subcommand)]
    command: InternalRescueCommand,
}

impl CommandDispatch for RescueCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        // None of the SPI commands care about the prior context, but they do
        // care about the `bus` parameter in the current node.
        self.command.run(self, transport)
    }
}
