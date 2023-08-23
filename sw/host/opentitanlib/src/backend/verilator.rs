// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use humantime::parse_duration;
use std::rc::Rc;
use std::time::Duration;

use crate::io::io_mapper::IoMapper;
use crate::transport::verilator::{Options, Verilator};
use crate::transport::Transport;

#[derive(Debug, Args)]
pub struct VerilatorOpts {
    #[arg(long, default_value_t)]
    verilator_bin: String,

    #[arg(long, default_value_t)]
    verilator_rom: String,
    #[arg(long, required = false)]
    verilator_flash: Vec<String>,
    #[arg(long, default_value_t)]
    verilator_otp: String,

    #[arg(long, required = false)]
    verilator_args: Vec<String>,

    /// Verilator startup timeout.
    #[arg(long, value_parser = parse_duration, default_value = "60s")]
    verilator_timeout: Duration,
}

pub fn create(args: &VerilatorOpts, io_mapper: Rc<IoMapper>) -> Result<Box<dyn Transport>> {
    let options = Options {
        executable: args.verilator_bin.clone(),
        rom_image: args.verilator_rom.clone(),
        flash_images: args.verilator_flash.clone(),
        otp_image: args.verilator_otp.clone(),
        extra_args: args.verilator_args.clone(),
        timeout: args.verilator_timeout,
    };
    Ok(Box::new(Verilator::from_options(options, io_mapper)?))
}
