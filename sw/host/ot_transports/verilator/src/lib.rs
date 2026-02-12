// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use humantime::parse_duration;
use std::time::Duration;

use opentitanlib::backend::{Backend, BackendOpts, define_interface};
use opentitanlib::transport::Transport;
use opentitanlib::util::fs::builtin_file;

pub mod gpio;
pub mod subprocess;
pub mod transport;

pub use subprocess::Options;
pub use transport::Verilator;

#[derive(Debug, Args)]
pub struct VerilatorOpts {
    #[arg(long, default_value_t)]
    verilator_bin: String,

    #[arg(long, required = false)]
    verilator_rom: Vec<String>,
    #[arg(long, required = false)]
    verilator_flash: Vec<String>,
    #[arg(long, default_value_t)]
    verilator_ctn_ram: String,
    #[arg(long, default_value_t)]
    verilator_otp: String,

    #[arg(long, required = false)]
    verilator_args: Vec<String>,

    /// Verilator startup timeout.
    #[arg(long, value_parser = parse_duration, default_value = "60s")]
    verilator_timeout: Duration,
}

struct VerilatorBackend;

impl Backend for VerilatorBackend {
    type Opts = VerilatorOpts;

    fn create_transport(_: &BackendOpts, args: &VerilatorOpts) -> Result<Box<dyn Transport>> {
        let options = Options {
            executable: args.verilator_bin.clone(),
            rom_images: args.verilator_rom.clone(),
            flash_images: args.verilator_flash.clone(),
            ctn_ram_image: args.verilator_ctn_ram.clone(),
            otp_image: args.verilator_otp.clone(),
            extra_args: args.verilator_args.clone(),
            timeout: args.verilator_timeout,
        };
        Ok(Box::new(Verilator::from_options(options)?))
    }
}

define_interface!(
    "verilator",
    VerilatorBackend,
    "/__builtin__/opentitan_verilator.json5"
);
builtin_file!(
    "opentitan_verilator.json5",
    include_str!("../config/opentitan_verilator.json5")
);
