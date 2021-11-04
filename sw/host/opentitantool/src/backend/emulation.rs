// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use opentitanlib::transport::emulation::HostEmulation;
use opentitanlib::transport::Transport;
use opentitanlib::util::parse_int::ParseInt;

use crate::backend::BackendOpts;

pub fn create(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(HostEmulation::new(
        match &args.usb_serial {
            Some(serial) => Some(u16::from_str(&serial)?),
            None => None,
        }
    )))
}
