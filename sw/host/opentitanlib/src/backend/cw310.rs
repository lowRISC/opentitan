// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::cw310::CW310;
use crate::transport::Transport;
use anyhow::Result;

use crate::backend::BackendOpts;

pub fn create(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(CW310::new(
        args.usb_vid,
        args.usb_vid,
        args.usb_serial.as_deref(),
    )?))
}
