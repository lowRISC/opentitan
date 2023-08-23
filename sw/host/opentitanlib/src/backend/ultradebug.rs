// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::ultradebug::Ultradebug;
use crate::transport::Transport;
use anyhow::Result;
use std::rc::Rc;

use crate::backend::BackendOpts;
use crate::io::io_mapper::IoMapper;

pub fn create(args: &BackendOpts, io_mapper: Rc<IoMapper>) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Ultradebug::new(
        args.usb_vid,
        args.usb_vid,
        args.usb_serial.clone(),
        io_mapper,
    )))
}
