// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::str::FromStr;
use std::time::Duration;
use std::time::Instant;
use structopt::clap::arg_enum;

use crate::io::uart::Uart;
use crate::uart::console::{ExitStatus, UartConsole};
use crate::util::usr_access::usr_access_get;

arg_enum! {
    #[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq)]
    pub enum RomKind {
        TestRom,
        Rom,
    }
}

pub struct RomDetect {
    kind: RomKind,
    usr_access: u32,
    console: UartConsole,
}

impl RomDetect {
    pub fn new(kind: RomKind, bitstream: &[u8], timeout: Option<Duration>) -> Result<RomDetect> {
        Ok(RomDetect {
            kind: kind,
            usr_access: usr_access_get(bitstream)?,
            console: UartConsole {
                timeout: timeout,
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
            let romkind = cap.get(1).unwrap().as_str();
            let kind = match RomKind::from_str(romkind) {
                Ok(k) => k,
                Err(_) => {
                    log::error!("Could not identify ROM kind {:?}", romkind);
                    return Ok(false);
                }
            };
            let fpga = cap
                .get(2)
                .map(|v| u32::from_str_radix(v.as_str(), 16))
                .unwrap()?;
            return Ok(kind == self.kind && fpga == self.usr_access);
        }
        log::info!("Did not detect the ROM identification message.");
        Ok(false)
    }
}
