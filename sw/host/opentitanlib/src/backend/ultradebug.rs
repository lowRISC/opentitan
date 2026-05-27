// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use opentitanlib_core::transport::Transport;
use opentitanlib_transports::ultradebug::Ultradebug;
use anyhow::Result;

use crate::BackendOpts;

pub fn create(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Ultradebug::new(
        args.usb_vid,
        args.usb_vid,
        args.usb_serial.clone(),
    )))
}
