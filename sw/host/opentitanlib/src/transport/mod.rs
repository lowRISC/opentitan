// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use bitflags::bitflags;
use erased_serde::Serialize;
use std::any::Any;
use std::path::PathBuf;
use std::rc::Rc;

use crate::io::gpio::GpioPin;
use crate::io::i2c::Bus;
use crate::io::spi::Target;
use crate::io::uart::Uart;

pub mod common;
pub mod cw310;
pub mod hyperdebug;
pub mod ultradebug;
pub mod verilator;

// Export custom error types
mod errors;
pub use errors::{Result, TransportError, TransportInterfaceType, WrapInTransportError};

bitflags! {
    /// A bitmap of capabilities which may be provided by a transport.
    pub struct Capability: u32 {
        const NONE = 0x00000000;
        const UART = 0x00000001;
        const SPI = 0x00000002;
        const GPIO = 0x00000004;
        const I2C = 0x00000008;
    }
}

/// A struct which can check that needed capability requirements are met.
pub struct Capabilities {
    capabilities: Capability,
    needed: Capability,
}

impl Capabilities {
    /// Create a new Capabilities object representing a provider of
    /// capabilities specified by `cap`.
    pub fn new(cap: Capability) -> Self {
        Self {
            capabilities: cap,
            needed: Capability::NONE,
        }
    }

    /// Request the capabilities specified by `cap`.
    pub fn request(&mut self, cap: Capability) -> &mut Self {
        self.needed |= cap;
        self
    }

    /// Checks that the requested capabilities are provided.
    pub fn ok(&self) -> anyhow::Result<()> {
        if self.capabilities & self.needed != self.needed {
            Err(anyhow::anyhow!(
                "Requested capabilities {:?}, but capabilities {:?} are supplied",
                self.needed,
                self.capabilities
            ))
        } else {
            Ok(())
        }
    }
}

/// A transport object is a factory for the low-level interfaces provided
/// by a given communications backend.
pub trait Transport {
    /// Returns a `Capabilities` object to check the capabilities of this
    /// transport object.
    fn capabilities(&self) -> Capabilities;

    /// Returns a SPI [`Target`] implementation.
    fn spi(&self, _instance: &str) -> Result<Rc<dyn Target>> {
        unimplemented!();
    }
    /// Returns a I2C [`Bus`] implementation.
    fn i2c(&self, _instance: &str) -> Result<Rc<dyn Bus>> {
        unimplemented!();
    }
    /// Returns a [`Uart`] implementation.
    fn uart(&self, _instance: &str) -> Result<Rc<dyn Uart>> {
        unimplemented!();
    }
    /// Returns a [`GpioPin`] implementation.
    fn gpio_pin(&self, _instance: &str) -> Result<Rc<dyn GpioPin>> {
        unimplemented!();
    }
    /// Invoke non-standard functionality of some Transport implementations.
    fn dispatch(&self, _action: &dyn Any) -> Result<Option<Box<dyn Serialize>>> {
        Err(TransportError::UnsupportedOperation.into())
    }
}

/// Used by Transport implementations dealing with emulated OpenTitan
/// chips, allowing e.g. more efficient direct means of programming
/// emulated flash storage.  (As opposed to running an actual
/// bootloater on the emulated target, which would receive data via
/// SPI to be flashed.)
pub struct Bootstrap {
    pub image_path: PathBuf,
}

/// An `EmptyTransport` provides no communications backend.
pub struct EmptyTransport;

impl Transport for EmptyTransport {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(Capability::NONE)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_capabilities_met() -> anyhow::Result<()> {
        let mut cap = Capabilities::new(Capability::UART | Capability::SPI);
        assert!(cap.request(Capability::UART).ok().is_ok());
        Ok(())
    }

    #[test]
    fn test_capabilities_not_met() -> anyhow::Result<()> {
        let mut cap = Capabilities::new(Capability::UART | Capability::SPI);
        assert!(cap.request(Capability::GPIO).ok().is_err());
        Ok(())
    }
}
