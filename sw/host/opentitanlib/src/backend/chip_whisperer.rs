// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::path::PathBuf;

use crate::backend::BackendOpts;
use crate::transport::chip_whisperer::board::Board;
use crate::transport::chip_whisperer::ChipWhisperer;
use crate::transport::Transport;

#[derive(Debug, Args)]
pub struct ChipWhispererOpts {
    /// Comma-separated list of Chip Whisperer board UARTs for non-udev environments. List the console uart first.
    #[arg(long, alias = "cw310-uarts")]
    pub uarts: Option<String>,

    /// Path to OpenOCD JTAG adapter config file to use (usually Olimex, but could be another
    /// adapter).
    #[arg(long)]
    pub openocd_adapter_config: Option<PathBuf>,
}

pub fn create<B: Board + 'static>(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    let uarts = args
        .opts
        .uarts
        .as_ref()
        .map(|v| v.split(',').collect::<Vec<&str>>())
        .unwrap_or_default();

    Ok(Box::new(ChipWhisperer::<B>::new(
        args.usb_vid,
        args.usb_pid,
        args.usb_serial.as_deref(),
        &uarts,
        args.opts.openocd_adapter_config.clone(),
    )?))
}
