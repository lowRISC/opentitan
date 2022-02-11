// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use crate::transport::ultradebug::Ultradebug;
use crate::transport::Transport;

use crate::backend::BackendOpts;

pub fn create(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Ultradebug::new(
        args.usb_vid,
        args.usb_vid,
        args.usb_serial.clone(),
    )))
}
