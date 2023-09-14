// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::i2c::{self, Bus};
use crate::transport::Transport;

use anyhow::Result;
use std::cell::Cell;
use std::rc::Rc;

/// Several `I2cWrapper` objects can exist concurrently, sharing the same underlying transport
/// bus, but having distinct I2C 7-bit address settings.  (Terminology is a little muddy here, in
/// that the wrapper also implements the I2C "bus" trait, even though it more properly would be
/// named a "target" or "device".)
///
/// Calling e.g. `set_max_speed()` on a `I2cWrapper` will not immediately be propagated to the
/// underlying transport, instead, the accumulated settings are kept in the `I2cWrapper`, and
/// propagated only whenever an actual I2C transaction is initiated.
pub struct I2cWrapper {
    /// Reference to the `Bus` instance of the underlying transport.
    underlying_target: Rc<dyn Bus>,
    my_default_addr: Cell<Option<u8>>,
    my_max_speed: Cell<Option<u32>>,
}

impl I2cWrapper {
    pub fn new(transport: &dyn Transport, conf: &super::I2cConfiguration) -> Result<Self> {
        Ok(Self {
            underlying_target: transport.i2c(conf.underlying_instance.as_str())?,
            my_default_addr: Cell::new(conf.default_addr),
            my_max_speed: Cell::new(conf.bits_per_sec),
        })
    }

    fn apply_settings_to_underlying(&self) -> Result<()> {
        if let Some(addr) = self.my_default_addr.get() {
            self.underlying_target.set_default_address(addr)?;
        }
        if let Some(speed) = self.my_max_speed.get() {
            self.underlying_target.set_max_speed(speed)?;
        }
        Ok(())
    }
}

impl Bus for I2cWrapper {
    fn get_max_speed(&self) -> Result<u32> {
        self.underlying_target.get_max_speed()
    }
    fn set_max_speed(&self, max_speed: u32) -> Result<()> {
        self.my_max_speed.set(Some(max_speed));
        Ok(())
    }

    fn set_default_address(&self, addr: u8) -> Result<()> {
        self.my_default_addr.set(Some(addr));
        Ok(())
    }

    fn run_transaction(&self, addr: Option<u8>, transaction: &mut [i2c::Transfer]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.underlying_target.run_transaction(addr, transaction)
    }
}
