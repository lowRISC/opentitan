// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::i2c::{self, Bus};
use crate::transport::Transport;

use anyhow::Result;
use std::cell::Cell;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Exactly one `PhysicalI2cWrapper` exists for every underlying tranport `Bus` instance that
/// has been accessed through the `TransportWrapper`.  It is used to keep track of which
/// `LogicalI2cWrapper` has already applied its settings to the hardware, in order to avoid
/// repeated invocations of e.g. `set_max_speed()` on the `Target`.
pub struct PhysicalI2cWrapper {
    /// Reference to the `Bus` instance of the underlying transport.
    underlying_target: Rc<dyn Bus>,
    /// Unique ID of the LogicalI2cWrapper which last used this physical I2C port.
    last_used_by_uid: Cell<Option<usize>>,
}

impl PhysicalI2cWrapper {
    /// Create new instance, should only be called from `TransportWrapper`
    pub fn new(underlying_target: Rc<dyn Bus>) -> Self {
        Self {
            underlying_target,
            last_used_by_uid: Cell::new(None),
        }
    }
}

/// Several `LogicalI2cWrapper` objects can exist concurrently, sharing the same underlying
/// transport bus, but having distinct I2C 7-bit address settings.  (Terminology is a little muddy
/// here, in that the wrapper also implements the I2C "bus" trait, even though it more properly
/// would be named a "target" or "device".)
///
/// Calling e.g. `set_max_speed()` on a `LogicalI2cWrapper` will not immediately be propagated to
/// the underlying transport, instead, the accumulated settings are kept in the
/// `LogicalI2cWrapper`, and propagated only whenever an actual I2C transaction is initiated.
pub struct LogicalI2cWrapper {
    /// Reference to the underlying port.
    physical_wrapper: Rc<PhysicalI2cWrapper>,
    /// Unique ID of this `LogicalI2cWrapper`.
    uid: usize,
    default_addr: Cell<Option<u8>>,
    max_speed: Cell<Option<u32>>,
}

impl LogicalI2cWrapper {
    pub fn new(
        _transport: &dyn Transport,
        conf: &super::I2cConfiguration,
        physical_wrapper: Rc<PhysicalI2cWrapper>,
    ) -> Result<Self> {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Ok(Self {
            physical_wrapper,
            uid: COUNTER.fetch_add(1, Ordering::Relaxed),
            default_addr: Cell::new(conf.default_addr),
            max_speed: Cell::new(conf.bits_per_sec),
        })
    }

    fn apply_settings_to_underlying(&self) -> Result<()> {
        if self.physical_wrapper.last_used_by_uid.get() == Some(self.uid) {
            // Physical I2C port last used by this same LogicalI2cWrapper, no need to re-apply our
            // settings.
            return Ok(());
        }
        if let Some(addr) = self.default_addr.get() {
            self.physical_wrapper
                .underlying_target
                .set_default_address(addr)?;
        }
        if let Some(speed) = self.max_speed.get() {
            self.physical_wrapper
                .underlying_target
                .set_max_speed(speed)?;
        }
        Ok(())
    }
}

impl Bus for LogicalI2cWrapper {
    fn get_max_speed(&self) -> Result<u32> {
        self.physical_wrapper.underlying_target.get_max_speed()
    }
    fn set_max_speed(&self, max_speed: u32) -> Result<()> {
        self.max_speed.set(Some(max_speed));
        Ok(())
    }

    fn set_default_address(&self, addr: u8) -> Result<()> {
        self.default_addr.set(Some(addr));
        Ok(())
    }

    fn run_transaction(&self, addr: Option<u8>, transaction: &mut [i2c::Transfer]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.physical_wrapper
            .underlying_target
            .run_transaction(addr, transaction)
    }
}
