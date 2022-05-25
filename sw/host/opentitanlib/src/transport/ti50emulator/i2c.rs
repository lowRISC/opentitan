// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::i2c::{Bus, Transfer};
use crate::transport::TransportError;
use anyhow::Result;

pub struct Ti50I2c {}

impl Bus for Ti50I2c {
    fn run_transaction(&self, _addr: u8, _transaction: &mut [Transfer]) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }
}
