// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use crate::BackendOpts;
use opentitanlib_core::transport::Transport;
use opentitanlib_transports::ftdi::Ftdi;
use opentitanlib_transports::ftdi::chip::Chip;

pub fn create<C: Chip + 'static>(_args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Ftdi::<C>::new()?))
}
