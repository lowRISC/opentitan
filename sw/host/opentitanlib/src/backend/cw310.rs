// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use structopt::StructOpt;

use crate::backend::BackendOpts;
use crate::transport::cw310::CW310;
use crate::transport::Transport;

#[derive(Debug, StructOpt)]
pub struct Cw310Opts {
    #[structopt(
        long,
        default_value,
        help = "Comma-separated list of CW310 UARTs for non-udev environments. List the console uart first."
    )]
    pub cw310_uarts: String,
}

pub fn create(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    let uarts = args
        .cw310_opts
        .cw310_uarts
        .split(',')
        .collect::<Vec<&str>>();
    Ok(Box::new(CW310::new(
        args.usb_vid,
        args.usb_vid,
        args.usb_serial.as_deref(),
        &uarts,
    )?))
}
