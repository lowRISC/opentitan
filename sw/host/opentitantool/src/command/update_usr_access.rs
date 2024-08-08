// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde_annotate::Annotate;
use std::any::Any;
use std::fs;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::util::parse_int::ParseInt;
use opentitanlib::util::usr_access::{usr_access_crc32, usr_access_set};

/// Update the USR_ACCESS value of an FPGA bitstream with the current timestamp.
#[derive(Debug, Args)]
pub struct UpdateUsrAccess {
    #[arg(name = "INPUT_FILE")]
    input: PathBuf,

    #[arg(name = "OUTPUT_FILE")]
    output: PathBuf,

    #[arg(
        long,
        value_parser = u32::from_str,
        help="New USR_ACCESS value, default = crc32"
    )]
    usr_access: Option<u32>,
}

impl CommandDispatch for UpdateUsrAccess {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let mut bs = fs::read(&self.input)?;

        let usr_access_val = match self.usr_access {
            None => usr_access_crc32(&mut bs)?,
            Some(u) => u,
        };
        usr_access_set(&mut bs, usr_access_val)?;

        fs::write(&self.output, bs)?;
        Ok(None)
    }
}
