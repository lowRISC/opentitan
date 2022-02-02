// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use opentitanlib::transport::hyperdebug::{Flavor, Hyperdebug};
use opentitanlib::transport::Transport;

use crate::backend::BackendOpts;

pub fn create<T: 'static + Flavor>(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Hyperdebug::<T>::open(
        args.usb_vid,
        args.usb_pid,
        args.usb_serial.as_deref(),
    )?))
}
