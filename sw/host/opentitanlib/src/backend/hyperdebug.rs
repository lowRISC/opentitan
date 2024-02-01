// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::hyperdebug::{Flavor, Hyperdebug, HyperdebugDfu};
use crate::transport::Transport;
use anyhow::Result;

use crate::backend::BackendOpts;

pub fn create<T: 'static + Flavor>(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Hyperdebug::<T>::open(
        args.usb_vid,
        args.usb_pid,
        args.usb_serial.as_deref(),
    )?))
}

pub fn create_dfu(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(HyperdebugDfu::open(
        args.usb_vid,
        args.usb_pid,
        args.usb_serial.as_deref(),
    )?))
}
