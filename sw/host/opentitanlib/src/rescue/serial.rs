// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::rc::Rc;
use std::time::Duration;

use anyhow::Result;
use regex::Regex;

use crate::app::{TransportWrapper, UartRx};
use crate::io::console::ConsoleExt;
use crate::io::console::ext::{PassFail, PassFailResult};
use crate::io::uart::Uart;
use crate::regex;
use crate::rescue::xmodem::Xmodem;
use crate::rescue::{EntryMode, Rescue, RescueError, RescueMode};

pub struct RescueSerial {
    uart: Rc<dyn Uart>,
    reset_delay: Duration,
    enter_delay: Duration,
    version: Cell<u16>,
}

impl RescueSerial {
    // The version is encoded in a u16 with the major as the high byte and minor as the low byte.
    const VERSION_1_0: u16 = 0x0100;
    const VERSION_2_0: u16 = 0x0200;

    const ONE_SECOND: Duration = Duration::from_secs(1);
    pub const REBOOT: RescueMode = RescueMode(u32::from_be_bytes(*b"REBO"));
    pub const BAUD: RescueMode = RescueMode(u32::from_be_bytes(*b"BAUD"));
    pub const WAIT: RescueMode = RescueMode(u32::from_be_bytes(*b"WAIT"));

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
            version: Cell::default(),
        }
    }
}

impl Rescue for RescueSerial {
    fn enter(&self, transport: &TransportWrapper, mode: EntryMode) -> Result<()> {
        log::info!("Setting serial break to trigger rescue mode (entry via {mode:?}).");
        match mode {
            EntryMode::Reset => {
                self.uart.set_break(true)?;
                transport.reset_with_delay(UartRx::Clear, self.reset_delay)?;
            }
            EntryMode::Reboot => {
                self.reboot()?;
                self.uart.set_break(true)?;
            }
            EntryMode::None => {
                self.uart.set_break(true)?;
            }
        }
        let version = (&self.uart).logged().wait_for_line(
            Regex::new(r"rescue:(?:(\d+)\.(\d+))?.*\r\n")?,
            self.enter_delay,
        )?;
        let version = if !version[1].is_empty() && !version[2].is_empty() {
            let major = version[1].parse::<u16>()?;
            let minor = version[2].parse::<u16>()?;
            (major << 8) | minor
        } else {
            0
        };
        self.version.set(version);
        log::info!("Rescue triggered (version={version:04x}). Clearing serial break.");
        self.uart.set_break(false)?;

        // Upon entry, rescue is going to tell us what mode it is.
        // Consume and discard.
        let _ = (&self.uart)
            .logged()
            .wait_for_line(PassFail("ok:", "error:"), Self::ONE_SECOND);

        if version < Self::VERSION_1_0 {
            // Make the older version of the protocol compliant with the current expectations of
            // the client.  Since the rescue client now expects the chip to wait after transfers
            // rather than automatically reset, we put older implementations into WAIT mode.
            self.set_mode(Self::WAIT)?;
        }
        if version >= Self::VERSION_2_0 {
            Err(RescueError::BadProtocol(format!(
                "This version of opentitantool does not support rescue protocol {version:04x}"
            ))
            .into())
        } else {
            Ok(())
        }
    }

    fn set_speed(&self, baud: u32) -> Result<u32> {
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

        // Request to change rates.  We don't use `set_mode` here because changing
        // rates isn't a "mode" request and doesn't respond the same way.
        self.uart.write(&Self::BAUD.0.to_be_bytes())?;
        self.uart.write(b"\r")?;
        if let PassFailResult::Fail(result) = (&self.uart)
            .logged()
            .wait_for_line(PassFail("ok:", regex!("error:.*")), Self::ONE_SECOND)?
        {
            return Err(RescueError::BadMode(result[0].clone()).into());
        }

        // Send the new rate and check for success.
        self.uart.write(&symbol)?;
        if let PassFailResult::Fail(result) = (&self.uart)
            .logged()
            .wait_for_line(PassFail("ok:", regex!("error:.*")), Self::ONE_SECOND)?
        {
            return Err(RescueError::BadMode(result[0].clone()).into());
        }
        // Change our side of the connection to the new rate.
        let old = self.uart.get_baudrate()?;
        self.uart.set_baudrate(baud)?;
        Ok(old)
    }

    fn set_mode(&self, mode: RescueMode) -> Result<()> {
        let mode = mode.0.to_be_bytes();
        self.uart.write(&mode)?;
        let enter = b'\r';
        self.uart.write(std::slice::from_ref(&enter))?;
        let mode = std::str::from_utf8(&mode)?;
        (&self.uart)
            .logged()
            .wait_for_line(format!("mode: {mode}").as_str(), Self::ONE_SECOND)?;
        if let PassFailResult::Fail(result) = (&self.uart)
            .logged()
            .wait_for_line(PassFail("ok:", regex!("error:.*")), Self::ONE_SECOND)?
        {
            return Err(RescueError::BadMode(format!("mode: {mode}\n{}", result[0])).into());
        }
        Ok(())
    }

    fn reboot(&self) -> Result<()> {
        self.set_mode(Self::REBOOT)?;
        Ok(())
    }

    fn send(&self, data: &[u8]) -> Result<()> {
        let xm = Xmodem::new();
        xm.send(&*self.uart, data)?;
        Ok(())
    }

    fn recv(&self) -> Result<Vec<u8>> {
        let mut data = Vec::new();
        let xm = Xmodem::new();
        xm.receive(&*self.uart, &mut data)?;
        Ok(data)
    }
}
