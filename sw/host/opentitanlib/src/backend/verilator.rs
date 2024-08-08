// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use humantime::parse_duration;
use std::time::Duration;

use crate::transport::verilator::{Options, Verilator};
use crate::transport::Transport;

#[derive(Debug, Args)]
pub struct VerilatorOpts {
    #[arg(long, default_value_t)]
    verilator_bin: String,

    #[arg(long, default_value_t)]
    verilator_rom: String,

    #[arg(long, required = false)]
    verilator_second_rom: Option<String>,

    #[arg(long, required = false)]
    verilator_flash: Vec<String>,
    #[arg(long, default_value_t)]
    verilator_otp: String,
    #[arg(long, default_value_t)]
    verilator_ram_ctn: String,

    #[arg(long, required = false)]
    verilator_args: Vec<String>,

    #[arg(long, value_parser = parse_duration, default_value = "60s", help = "Verilator startup timeout")]
    verilator_timeout: Duration,
}

pub fn create(args: &VerilatorOpts) -> Result<Box<dyn Transport>> {
    let options = Options {
        executable: args.verilator_bin.clone(),
        rom_image: args.verilator_rom.clone(),
        second_rom_image: args.verilator_second_rom.clone(),
        flash_images: args.verilator_flash.clone(),
        otp_image: args.verilator_otp.clone(),
        ram_ctn_image: args.verilator_ram_ctn.clone(),
        extra_args: args.verilator_args.clone(),
        timeout: args.verilator_timeout,
    };
    Ok(Box::new(Verilator::from_options(options)?))
}
