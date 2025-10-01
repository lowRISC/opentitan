// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use super::{Backend, BackendOpts, define_interface};
use crate::transport::Transport;
use crate::transport::ftdi::Ftdi;
use crate::transport::ftdi::chip::{Chip, Ft4232hq};

struct FtdiBackend<C>(C);

impl<C: Chip + 'static> Backend for FtdiBackend<C> {
    type Opts = ();

    fn create_transport(_: &BackendOpts, _: &()) -> Result<Box<dyn Transport>> {
        Ok(Box::new(Ftdi::<C>::new()?))
    }
}

define_interface!(
    "ftdi",
    FtdiBackend<Ft4232hq>,
    "/__builtin__/opentitan_ftdi_voyager.json5"
);
