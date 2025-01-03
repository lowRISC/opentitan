// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use crate::backend::BackendOpts;
use crate::transport::ftdi::chip::Chip;
use crate::transport::ftdi::Ftdi;
use crate::transport::Transport;

pub fn create<C: Chip + 'static>(_args: &BackendOpts) -> Result<Box<dyn Transport>> {
    Ok(Box::new(Ftdi::<C>::new()?))
}
