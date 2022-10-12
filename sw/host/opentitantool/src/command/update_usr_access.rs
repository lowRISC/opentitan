// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde_annotate::Annotate;
use std::any::Any;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::util::parse_int::ParseInt;
use opentitanlib::util::usr_access::{usr_access_set, usr_access_timestamp};

/// Update the USR_ACCESS value of an FPGA bitstream with the current timestamp.
#[derive(Debug, StructOpt)]
pub struct UpdateUsrAccess {
    #[structopt(name = "INPUT_FILE")]
    input: PathBuf,

    #[structopt(name = "OUTPUT_FILE")]
    output: PathBuf,

    #[structopt(long,
                parse(try_from_str = u32::from_str),
                help="New USR_ACCESS value, default = timestamp")]
    usr_access: Option<u32>,
}

impl CommandDispatch for UpdateUsrAccess {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let mut bs = fs::read(&self.input)?;
        usr_access_set(
            &mut bs,
            self.usr_access.unwrap_or_else(usr_access_timestamp),
        )?;
        fs::write(&self.output, bs)?;
        Ok(None)
    }
}
