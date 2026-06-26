// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::Transport;
use crate::transport::hyperdebug::{Flavor, Hyperdebug, HyperdebugDfu};
use anyhow::Result;
use clap::Args;

use crate::backend::BackendOpts;

#[derive(Debug, Args)]
pub struct HyperdebugOpts {
    /// Work around the USB transceiver on the CW boards not being disabled when the FPGA is
    /// is not loaded. Enabling this option will cause the backend to disable the USB port
    /// prior to clearing the bitstream and only re-enable it after loading. It assumes that
    /// the USB port is connected to the same parent hub as the hyperdebug device and this option
    /// specifies the port number of that hub.
    #[arg(long)]
    pub cw_usb_port_workaround: Option<u8>,
}

pub fn create<T: 'static + Flavor>(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Hyperdebug::<T>::open(
        args.usb_vid,
        args.usb_pid,
        args.usb_serial.as_deref(),
        args.hyperdebug_opts.cw_usb_port_workaround,
    )?))
}

pub fn create_dfu(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(HyperdebugDfu::open(
        args.usb_vid,
        args.usb_pid,
        args.usb_serial.as_deref(),
    )?))
}
