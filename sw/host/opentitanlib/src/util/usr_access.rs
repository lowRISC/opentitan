// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::convert::TryInto;
use thiserror::Error;

const WRITE_USR_ACCESS: [u8; 4] = [0x30, 0x01, 0xa0, 0x01];

#[derive(Error, Debug, Serialize, Deserialize)]
pub enum Error {
    #[error("Command {0:#x?} not found in bitstream")]
    CommandNotFound(u32),
}

fn find_cmd(bitstream: &[u8], cmd: &[u8; 4]) -> Result<usize> {
    Ok(bitstream
        .chunks(4)
        .enumerate()
        .find(|(_, op)| *op == cmd)
        .ok_or(Error::CommandNotFound(u32::from_be_bytes(*cmd)))?
        .0
        * 4)
}


pub fn usr_access_get(bitstream: &[u8]) -> Result<u32> {
    let i = find_cmd(&bitstream, &WRITE_USR_ACCESS)?;
    if (i + 8) > bitstream.len() {
        return Err(Error::CommandNotFound(u32::from_be_bytes(WRITE_USR_ACCESS)).into());
    }
    let operand = &bitstream[i + 4..i + 8];
    let usr_access = u32::from_be_bytes(operand.try_into()?);
    log::info!("Bitstream file USR_ACCESS value: {:#x}", usr_access);
    Ok(usr_access)
}

