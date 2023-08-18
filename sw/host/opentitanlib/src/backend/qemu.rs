// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::ffi::OsString;
use std::path::PathBuf;
use std::time::Duration;

use clap::Args;
use humantime::parse_duration;

use crate::transport::qemu::{Options, Qemu};
use crate::transport::Transport;

#[derive(Debug, Args)]
pub struct QemuOpts {
    /// Path to a QEMU binary to use.
    #[arg(long, default_value = "qemu-system-riscv32")]
    pub qemu_bin: PathBuf,

    /// Name of the QEMU machine to execute.
    #[arg(long, default_value = "ot-earlgrey")]
    pub qemu_machine: String,

    /// Additional properties for the QEMU machine.
    #[arg(long, required = false)]
    pub qemu_machine_prop: Vec<String>,

    /// Path to a ROM image to be used.
    #[arg(long)]
    pub qemu_rom: Option<PathBuf>,

    /// Path to the flash image to use.
    #[arg(long)]
    pub qemu_flash: Option<PathBuf>,

    /// Path to the OTP image to use.
    #[arg(long)]
    pub qemu_otp: Option<PathBuf>,

    /// Additional arguments to pass to QEMU.
    #[arg(long, required = false, num_args = 0..)]
    #[arg(allow_hyphen_values = true, value_terminator = ";")]
    pub qemu_args: Vec<OsString>,

    /// QEMU startup timeout.
    #[arg(long, value_parser = parse_duration, default_value = "60s")]
    pub qemu_timeout: Duration,
}

/// Create a [`Qemu`] transport based on some command line options.
pub fn create(args: &QemuOpts) -> anyhow::Result<Box<dyn Transport>> {
    let options = Options {
        executable: args.qemu_bin.clone(),
        machine: args.qemu_machine.clone(),
        machine_props: args.qemu_machine_prop.clone(),
        rom_image: args.qemu_rom.clone(),
        flash_image: args.qemu_flash.clone(),
        otp_image: args.qemu_otp.clone(),
        extra_args: args.qemu_args.clone(),
        timeout: args.qemu_timeout,
    };
    Ok(Box::new(Qemu::from_options(options)?))
}
