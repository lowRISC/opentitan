// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use humantime::parse_duration;
use std::time::Duration;
use structopt::StructOpt;

use crate::transport::verilator::{Options, Verilator};
use crate::transport::Transport;

#[derive(Debug, StructOpt)]
pub struct VerilatorOpts {
    #[structopt(long, default_value)]
    verilator_bin: String,

    #[structopt(long, default_value)]
    verilator_rom: String,
    #[structopt(long, required = false)]
    verilator_flash: Vec<String>,
    #[structopt(long, default_value)]
    verilator_otp: String,

    #[structopt(long, required = false)]
    verilator_args: Vec<String>,

    #[structopt(long, parse(try_from_str=parse_duration), default_value="60s", help = "Verilator startup timeout")]
    verilator_timeout: Duration,
}

pub fn create(args: &VerilatorOpts) -> Result<Box<dyn Transport>> {
    let options = Options {
        executable: args.verilator_bin.clone(),
        rom_image: args.verilator_rom.clone(),
        flash_images: args.verilator_flash.clone(),
        otp_image: args.verilator_otp.clone(),
        extra_args: args.verilator_args.clone(),
        timeout: args.verilator_timeout,
    };
    Ok(Box::new(Verilator::from_options(options)?))
}
