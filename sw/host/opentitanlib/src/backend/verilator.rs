// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::verilator::{Options, Verilator};
use crate::transport::Transport;
use anyhow::Result;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
pub struct VerilatorOpts {
    #[structopt(long, default_value)]
    verilator_bin: String,

    #[structopt(long, default_value)]
    verilator_rom: String,
    #[structopt(long, default_value)]
    verilator_flash: String,
    #[structopt(long, default_value)]
    verilator_otp: String,

    #[structopt(long, required = false)]
    verilator_args: Vec<String>,
}

pub fn create(args: &VerilatorOpts) -> Result<Box<dyn Transport>> {
    let options = Options {
        executable: args.verilator_bin.clone(),
        rom_image: args.verilator_rom.clone(),
        flash_image: args.verilator_flash.clone(),
        otp_image: args.verilator_otp.clone(),
        extra_args: args.verilator_args.clone(),
    };
    Ok(Box::new(Verilator::from_options(options)?))
}
