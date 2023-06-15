// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;

use crate::backend::BackendOpts;
use crate::transport::cw310::CW310;
use crate::transport::Transport;

#[derive(Debug, Args)]
pub struct Cw310Opts {
    #[arg(
        long,
        help = "Comma-separated list of CW310 UARTs for non-udev environments. List the console uart first."
    )]
    pub cw310_uarts: Option<String>,
}

pub fn create(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    let uarts = args
        .cw310_opts
        .cw310_uarts
        .as_ref()
        .map(|v| v.split(',').collect::<Vec<&str>>())
        .unwrap_or_default();
    Ok(Box::new(CW310::new(
        args.usb_vid,
        args.usb_pid,
        args.usb_serial.as_deref(),
        &uarts,
    )?))
}
