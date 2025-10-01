// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use super::{Backend, BackendOpts, define_interface};
use crate::transport::Transport;
use crate::transport::dediprog::Dediprog;

struct DediprogBackend;

impl Backend for DediprogBackend {
    type Opts = ();

    fn create_transport(args: &BackendOpts, _: &()) -> Result<Box<dyn Transport>> {
        Ok(Box::new(Dediprog::new(
            args.usb_vid,
            args.usb_pid,
            args.usb_serial.as_deref(),
        )?))
    }
}

define_interface!("dediprog", DediprogBackend, "/__builtin__/dediprog.json5");
