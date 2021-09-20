// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use bitflags::bitflags;
use std::rc::Rc;
use thiserror::Error;

use crate::io::gpio::Gpio;
use crate::io::spi::Target;
use crate::io::uart::Uart;

pub mod cw310;
pub mod ultradebug;
pub mod verilator;

bitflags! {
    /// A bitmap of capabilities which may be provided by a transport.
    pub struct Capability: u32 {
        const NONE = 0x00000000;
        const UART = 0x00000001;
        const SPI = 0x00000002;
        const GPIO = 0x00000004;
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
    pub fn ok(&self) -> Result<()> {
        if self.capabilities & self.needed != self.needed {
            Err(anyhow!(
                "Requested capabilities {:?}, but capabilities {:?} are supplied",
                self.needed,
                self.capabilities
            ))
        } else {
            Ok(())
        }
    }
}

/// Errors related to the SPI interface and SPI transactions.
#[derive(Error, Debug)]
pub enum TransportError {
    #[error("This transport does not support {0} instance {1}")]
    InvalidInstance(&'static str, u32),
}

/// A transport object is a factory for the low-level interfaces provided
/// by a given communications backend.
pub trait Transport {
    /// Returns a `Capabilities` object to check the capabilities of this
    /// transport object.
    fn capabilities(&self) -> Capabilities;

    /// Returns a SPI [`Target`] implementation.
    fn spi(&self, _instance: u32) -> Result<Rc<dyn Target>> {
        unimplemented!();
    }
    /// Returns a [`Uart`] implementation.
    fn uart(&self, _instance: u32) -> Result<Rc<dyn Uart>> {
        unimplemented!();
    }
    /// Returns a [`Gpio`] implementation.
    fn gpio(&self) -> Result<Rc<dyn Gpio>> {
        unimplemented!();
    }
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
    fn test_capabilities_met() -> Result<()> {
        let mut cap = Capabilities::new(Capability::UART | Capability::SPI);
        assert!(cap.request(Capability::UART).ok().is_ok());
        Ok(())
    }

    #[test]
    fn test_capabilities_not_met() -> Result<()> {
        let mut cap = Capabilities::new(Capability::UART | Capability::SPI);
        assert!(cap.request(Capability::GPIO).ok().is_err());
        Ok(())
    }
}
