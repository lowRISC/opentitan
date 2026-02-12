// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;

use crate::io::console::ConsoleExt;
use crate::io::uart::Uart;
use crate::regex;
use crate::util::usr_access::usr_access_get;

pub struct RomDetect {
    usr_access: u32,
    timeout: Duration,
}

impl RomDetect {
    pub fn new(bitstream: &[u8], timeout: Option<Duration>) -> Result<RomDetect> {
        Ok(RomDetect {
            usr_access: usr_access_get(bitstream)?,
            timeout: timeout.unwrap_or(Duration::MAX),
        })
    }

    pub fn detect(&mut self, uart: &dyn Uart) -> Result<bool> {
        if let Some(cap) = uart.try_wait_for_line(regex!(r"(\w*ROM):([^\r\n]+)"), self.timeout)? {
            log::info!("Current bitstream: {:?}", cap[0]);
            let fpga = u32::from_str_radix(&cap[2], 16)?;
            return Ok(fpga == self.usr_access);
        }

        log::info!("Did not detect the ROM identification message.");
        Ok(false)
    }
}
