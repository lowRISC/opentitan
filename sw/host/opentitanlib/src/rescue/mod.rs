// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, ensure};
use clap::{Args, ValueEnum};
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::chip::boot_log::BootLog;
use crate::chip::boot_svc::{BootSlot, BootSvc, OwnershipActivateRequest, OwnershipUnlockRequest};
use crate::chip::device_id::DeviceId;
use crate::io::uart::UartParams;
use crate::with_unknown;

pub mod serial;
pub mod xmodem;

pub use serial::RescueSerial;

#[derive(Debug, Error)]
pub enum RescueError {
    #[error("bad mode: {0}")]
    BadMode(String),
    #[error("configuration error: {0}")]
    Configuration(String),
    #[error("bad protocol: {0}")]
    BadProtocol(String),
}

#[derive(ValueEnum, Default, Debug, Clone, Copy, PartialEq)]
pub enum RescueProtocol {
    #[default]
    Xmodem,
    UsbDfu,
    SpiDfu,
}

#[derive(ValueEnum, Default, Debug, Clone, Copy, PartialEq)]
pub enum RescueTrigger {
    #[default]
    SerialBreak,
    Gpio,
    Strap,
}

#[derive(Clone, Default, Debug, Args)]
pub struct RescueParams {
    /// Rescue Protocol
    #[arg(short, long, value_enum, default_value_t = RescueProtocol::Xmodem)]
    pub protocol: RescueProtocol,
    #[arg(short, long, value_enum, default_value_t = RescueTrigger::SerialBreak)]
    pub trigger: RescueTrigger,
    #[arg(short, long, default_value = "")]
    pub value: String,
    #[command(flatten)]
    uart: UartParams,
}

impl RescueParams {
    pub fn create(&self, transport: &TransportWrapper) -> Result<Box<dyn Rescue>> {
        match self.protocol {
            RescueProtocol::Xmodem => self.create_serial(transport),
            RescueProtocol::UsbDfu => self.create_usbdfu(transport),
            RescueProtocol::SpiDfu => self.create_spidfu(transport),
        }
    }
    fn create_serial(&self, transport: &TransportWrapper) -> Result<Box<dyn Rescue>> {
        ensure!(
            self.trigger == RescueTrigger::SerialBreak,
            RescueError::Configuration(format!(
                "Xmodem does not support trigger {:?}",
                self.trigger
            ))
        );
        ensure!(
            self.value.is_empty(),
            RescueError::Configuration(format!(
                "Xmodem does not support trigger value {:?}",
                self.value
            ))
        );

        Ok(Box::new(RescueSerial::new(self.uart.create(transport)?)))
    }
    fn create_usbdfu(&self, _transport: &TransportWrapper) -> Result<Box<dyn Rescue>> {
        unimplemented!()
    }
    fn create_spidfu(&self, _transport: &TransportWrapper) -> Result<Box<dyn Rescue>> {
        unimplemented!()
    }
}

with_unknown! {
pub enum RescueMode: u32 {
    Rescue = u32::from_be_bytes(*b"RESQ"),
    RescueB = u32::from_be_bytes(*b"RESB"),
    BootLog = u32::from_be_bytes(*b"BLOG"),
    BootSvcReq = u32::from_be_bytes(*b"BREQ"),
    BootSvcRsp = u32::from_be_bytes(*b"BRSP"),
    OwnerBlock = u32::from_be_bytes(*b"OWNR"),
    GetOwnerPage0 = u32::from_be_bytes(*b"OPG0"),
    GetOwnerPage1 = u32::from_be_bytes(*b"OPG1"),
    DeviceId = u32::from_be_bytes(*b"OTID"),
    EraseOwner = u32::from_be_bytes(*b"KLBR"),
}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
/// Determines how `Rescue::enter` should enter rescue mode.
pub enum EntryMode {
    /// Reset the chip using the external power-on reset signal.
    Reset,
    /// Assume the chip is in rescue mode and needs to soft-reboot back to rescue mode.
    Reboot,
    /// Do nothing; assume the chip is ready to go to rescue mode.
    None,
}

pub trait Rescue {
    fn enter(&self, transport: &TransportWrapper, mode: EntryMode) -> Result<()>;
    fn set_mode(&self, mode: RescueMode) -> Result<()>;
    fn send(&self, data: &[u8]) -> Result<()>;
    fn recv(&self) -> Result<Vec<u8>>;

    // Not supported by all backends
    fn set_speed(&self, speed: u32) -> Result<u32>;
    fn reboot(&self) -> Result<()>;

    fn get_raw(&self, mode: RescueMode) -> Result<Vec<u8>> {
        self.set_mode(mode)?;
        self.recv()
    }

    fn set_raw(&self, mode: RescueMode, data: &[u8]) -> Result<()> {
        self.set_mode(mode)?;
        self.send(data)
    }

    fn update_firmware(&self, slot: BootSlot, image: &[u8]) -> Result<()> {
        let mode = if slot == BootSlot::SlotB {
            RescueMode::RescueB
        } else {
            RescueMode::Rescue
        };
        self.set_raw(mode, image)
    }

    fn get_boot_log(&self) -> Result<BootLog> {
        let blog = self.get_raw(RescueMode::BootLog)?;
        Ok(BootLog::try_from(blog.as_slice())?)
    }

    fn get_boot_svc(&self) -> Result<BootSvc> {
        let bsvc = self.get_raw(RescueMode::BootSvcRsp)?;
        Ok(BootSvc::try_from(bsvc.as_slice())?)
    }

    fn get_device_id(&self) -> Result<DeviceId> {
        let id = self.get_raw(RescueMode::DeviceId)?;
        DeviceId::read(&mut std::io::Cursor::new(&id))
    }

    fn set_next_bl0_slot(&self, primary: BootSlot, next: BootSlot) -> Result<()> {
        let message = BootSvc::next_boot_bl0_slot(primary, next);
        self.set_raw(RescueMode::BootSvcReq, &message.to_bytes()?)
    }

    fn ownership_unlock(&self, unlock: OwnershipUnlockRequest) -> Result<()> {
        let message = BootSvc::ownership_unlock(unlock);
        self.set_raw(RescueMode::BootSvcReq, &message.to_bytes()?)
    }

    fn ownership_activate(&self, activate: OwnershipActivateRequest) -> Result<()> {
        let message = BootSvc::ownership_activate(activate);
        self.set_raw(RescueMode::BootSvcReq, &message.to_bytes()?)
    }

    fn set_owner_config(&self, data: &[u8]) -> Result<()> {
        self.set_raw(RescueMode::OwnerBlock, data)
    }

    fn erase_owner(&self) -> Result<()> {
        self.set_raw(RescueMode::EraseOwner, &[])
    }
}
