// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::convert::TryInto;
use std::str::FromStr;
use std::time::Duration;
use structopt::clap::arg_enum;
use thiserror::Error;

use crate::io::uart::Uart;
use crate::uart::console::{ExitStatus, UartConsole};

const REG_USR_ACCESS: [u8; 4] = [0x30, 0x01, 0xa0, 0x01];

#[derive(Error, Debug, Serialize, Deserialize)]
pub enum Error {
    #[error("USR_ACCESS value not found in bitstream")]
    UsrAccessNotFound,
}

arg_enum! {
    #[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq)]
    pub enum RomKind {
        TestRom,
        MaskRom,
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
            usr_access: Self::scan_usr_access(bitstream)?,
            console: UartConsole {
                timeout: timeout,
                exit_success: Some(Regex::new(r"(\w+ROM):([^\r\n]*)").unwrap()),
                ..Default::default()
            },
        })
    }

    fn scan_usr_access(bitstream: &[u8]) -> Result<u32> {
        let operand = bitstream
            .chunks(4)
            .skip_while(|op| **op != REG_USR_ACCESS)
            .nth(1)
            .ok_or(Error::UsrAccessNotFound)?;
        let usr_access = u32::from_be_bytes(operand.try_into()?);
        log::info!("Bitstream USR_ACCESS value: {:#x}", usr_access);
        Ok(usr_access)
    }

    pub fn detect(&mut self, uart: &dyn Uart) -> Result<bool> {
        self.console.interact(uart, None, None)?;
        if let Some(cap) = self.console.captures(ExitStatus::ExitSuccess) {
            log::info!("Found: {:?}", cap.get(0).unwrap().as_str());
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
