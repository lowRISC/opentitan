// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use regex::Regex;
use std::time::Duration;
use std::time::Instant;

use crate::io::uart::Uart;
use crate::uart::console::{ExitStatus, UartConsole};
use crate::util::usr_access::usr_access_get;

pub struct RomDetect {
    usr_access: u32,
    console: UartConsole,
}

impl RomDetect {
    pub fn new(bitstream: &[u8], timeout: Option<Duration>) -> Result<RomDetect> {
        Ok(RomDetect {
            usr_access: usr_access_get(bitstream)?,
            console: UartConsole {
                timeout,
                exit_success: Some(Regex::new(r"(\w*ROM):([^\r\n]+)[\r\n]").unwrap()),
                ..Default::default()
            },
        })
    }

    pub fn detect(&mut self, uart: &dyn Uart) -> Result<bool> {
        let t0 = Instant::now();
        let rc = self.console.interact(uart, None, None)?;
        let t1 = Instant::now();
        log::debug!("detect exit={:?}, duration={:?}", rc, t1 - t0);
        if let Some(cap) = self.console.captures(ExitStatus::ExitSuccess) {
            log::info!("Current bitstream: {:?}", cap.get(0).unwrap().as_str());
            let fpga = cap
                .get(2)
                .map(|v| u32::from_str_radix(v.as_str(), 16))
                .unwrap()?;
            return Ok(fpga == self.usr_access);
        }
        log::info!("Did not detect the ROM identification message.");
        Ok(false)
    }
}
