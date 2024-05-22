// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::rc::Rc;
use std::time::Duration;

use crate::app::TransportWrapper;
use crate::chip::boot_log::BootLog;
use crate::chip::boot_svc::{BootSlot, BootSvc, OwnershipActivateRequest, OwnershipUnlockRequest};
use crate::io::uart::Uart;
use crate::rescue::xmodem::Xmodem;
use crate::rescue::RescueError;
use crate::uart::console::UartConsole;

pub struct RescueSerial {
    uart: Rc<dyn Uart>,
    reset_delay: Duration,
    enter_delay: Duration,
}

impl RescueSerial {
    const ONE_SECOND: Duration = Duration::from_secs(1);
    pub const RESCUE: [u8; 4] = *b"RESQ";
    pub const RESCUE_B: [u8; 4] = *b"RESB";
    pub const REBOOT: [u8; 4] = *b"REBO";
    pub const BAUD: [u8; 4] = *b"BAUD";
    pub const BOOT_LOG: [u8; 4] = *b"BLOG";
    pub const BOOT_SVC_REQ: [u8; 4] = *b"BREQ";
    pub const BOOT_SVC_RSP: [u8; 4] = *b"BRSP";
    pub const OWNER_BLOCK: [u8; 4] = *b"OWNR";
    pub const WAIT: [u8; 4] = *b"WAIT";

    const BAUD_115K: [u8; 4] = *b"115K";
    const BAUD_230K: [u8; 4] = *b"230K";
    const BAUD_460K: [u8; 4] = *b"460K";
    const BAUD_921K: [u8; 4] = *b"921K";
    const BAUD_1M33: [u8; 4] = *b"1M33";
    const BAUD_1M50: [u8; 4] = *b"1M50";

    pub fn new(uart: Rc<dyn Uart>) -> Self {
        RescueSerial {
            uart,
            reset_delay: Duration::from_millis(50),
            enter_delay: Duration::from_secs(5),
        }
    }

    pub fn enter(&self, transport: &TransportWrapper) -> Result<()> {
        log::info!("Setting serial break to trigger rescue mode.");
        self.uart.set_break(true)?;
        transport.reset_target(self.reset_delay, /*clear_uart*=*/ true)?;
        UartConsole::wait_for(&*self.uart, r"rescue:.*\r\n", self.enter_delay)?;
        log::info!("Rescue triggered. clearing serial break.");
        self.uart.set_break(false)?;
        // Upon entry, rescue is going to tell us what mode it is.
        // Consume and discard.
        let _ = UartConsole::wait_for(&*self.uart, r"(ok|error):.*\r\n", Self::ONE_SECOND);
        Ok(())
    }

    pub fn set_baud(&self, baud: u32) -> Result<()> {
        // Make sure the requested rate is a known rate.
        let symbol = match baud {
            115200 => Self::BAUD_115K,
            230400 => Self::BAUD_230K,
            460800 => Self::BAUD_460K,
            921600 => Self::BAUD_921K,
            1333333 => Self::BAUD_1M33,
            1500000 => Self::BAUD_1M50,
            _ => return Err(RescueError::BadMode(format!("Unsupported badrate {baud}")).into()),
        };

        // Request to change rates.
        self.set_mode(Self::BAUD)?;

        // Send the new rate and check for success.
        self.uart.write(&symbol)?;
        let result = UartConsole::wait_for(&*self.uart, r"(ok|error):.*\r\n", Self::ONE_SECOND)?;
        if result[1] == "error" {
            return Err(RescueError::BadMode(result[0].clone()).into());
        }
        // Change our side of the connection to the new rate.
        self.uart.set_baudrate(baud)?;
        Ok(())
    }

    pub fn set_mode(&self, mode: [u8; 4]) -> Result<()> {
        self.uart.write(&mode)?;
        let enter = b'\r';
        self.uart.write(std::slice::from_ref(&enter))?;
        let result = UartConsole::wait_for(&*self.uart, r"(ok|error):.*\r\n", Self::ONE_SECOND)?;
        if result[1] == "error" {
            return Err(RescueError::BadMode(result[0].clone()).into());
        }
        Ok(())
    }

    pub fn wait(&self) -> Result<()> {
        self.set_mode(Self::WAIT)?;
        Ok(())
    }

    pub fn reboot(&self) -> Result<()> {
        self.set_mode(Self::REBOOT)?;
        Ok(())
    }

    pub fn update_firmware(&self, slot: BootSlot, image: &[u8]) -> Result<()> {
        self.set_mode(if slot == BootSlot::SlotB {
            Self::RESCUE_B
        } else {
            Self::RESCUE
        })?;
        let xm = Xmodem::new();
        xm.send(&*self.uart, image)?;
        Ok(())
    }

    pub fn get_boot_log_raw(&self) -> Result<Vec<u8>> {
        self.set_mode(Self::BOOT_LOG)?;
        let mut blog = Vec::new();
        let xm = Xmodem::new();
        xm.receive(&*self.uart, &mut blog)?;
        Ok(blog)
    }

    pub fn get_boot_log(&self) -> Result<BootLog> {
        let blog = self.get_boot_log_raw()?;
        Ok(BootLog::try_from(blog.as_slice())?)
    }

    pub fn get_boot_svc_raw(&self) -> Result<Vec<u8>> {
        self.set_mode(Self::BOOT_SVC_RSP)?;
        let mut bsvc = Vec::new();
        let xm = Xmodem::new();
        xm.receive(&*self.uart, &mut bsvc)?;
        Ok(bsvc)
    }

    pub fn get_boot_svc(&self) -> Result<BootSvc> {
        let bsvc = self.get_boot_svc_raw()?;
        Ok(BootSvc::try_from(bsvc.as_slice())?)
    }

    pub fn set_boot_svc_raw(&self, data: &[u8]) -> Result<()> {
        self.set_mode(Self::BOOT_SVC_REQ)?;
        let xm = Xmodem::new();
        xm.send(&*self.uart, data)?;
        Ok(())
    }

    pub fn set_next_bl0_slot(&self, slot: BootSlot) -> Result<()> {
        let message = BootSvc::next_boot_bl0_slot(slot);
        let data = message.to_bytes()?;
        self.set_boot_svc_raw(&data)
    }

    pub fn set_primary_bl0_slot(&self, slot: BootSlot) -> Result<()> {
        let message = BootSvc::primary_bl0_slot(slot);
        let data = message.to_bytes()?;
        self.set_boot_svc_raw(&data)
    }

    pub fn ownership_unlock(&self, unlock: OwnershipUnlockRequest) -> Result<()> {
        let message = BootSvc::ownership_unlock(unlock);
        let data = message.to_bytes()?;
        self.set_boot_svc_raw(&data)
    }

    pub fn ownership_activate(&self, activate: OwnershipActivateRequest) -> Result<()> {
        let message = BootSvc::ownership_activate(activate);
        let data = message.to_bytes()?;
        self.set_boot_svc_raw(&data)
    }

    pub fn set_owner_config(&self, data: &[u8]) -> Result<()> {
        self.set_mode(Self::OWNER_BLOCK)?;
        let xm = Xmodem::new();
        xm.send(&*self.uart, data)?;
        Ok(())
    }
}
