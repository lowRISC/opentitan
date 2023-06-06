// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::ti50emulator::Ti50Emulator;
use crate::transport::Transport;
use anyhow::Result;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
pub struct Ti50EmulatorOpts {
    #[structopt(long, default_value = "ti50")]
    instance_prefix: String,

    #[structopt(long, parse(from_os_str), default_value = "")]
    executable_directory: PathBuf,

    #[structopt(long, default_value = "")]
    executable: String,
}

pub fn create(args: &Ti50EmulatorOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Ti50Emulator::open(
        &args.executable_directory,
        &args.executable,
        &args.instance_prefix,
    )?))
}
