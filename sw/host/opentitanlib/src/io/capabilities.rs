// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Transport capabilities checking.

use anyhow::Result;
use bitflags::bitflags;
use serde::{Deserialize, Serialize};

use crate::io::TransportError;

bitflags! {
    /// A bitmap of capabilities which may be provided by a transport.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
    #[serde(transparent)]
    pub struct Capability: u32 {
        const NONE = 0x00;
        const UART = 0x01 << 0;
        const SPI = 0x01 << 1;
        const GPIO = 0x01 << 2;
        const I2C = 0x01 << 3;
        const PROXY = 0x01 << 4;
        const EMULATOR = 0x01 << 5;
        const GPIO_MONITORING = 0x01 << 6; // Logic analyzer functionality
        const JTAG = 0x01 << 7;
        const UART_NONBLOCKING = 0x01 << 8;
        const SPI_DUAL = 0x01 << 9;
        const SPI_QUAD = 0x01 << 10;
        const GPIO_BITBANGING = 0x01 << 11;
        const USB = 0x01 << 12;
    }
}

/// A struct which represents what features a particular Transport instance supports.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct Capabilities {
    capabilities: Capability,
}

impl Capabilities {
    /// Create a new Capabilities object representing a provider of
    /// capabilities specified by `cap`.
    pub fn new(cap: Capability) -> Self {
        Self { capabilities: cap }
    }

    pub fn add(&self, extra: Capability) -> Self {
        Self {
            capabilities: self.capabilities | extra,
        }
    }

    /// Request the capabilities specified by `cap`.
    pub fn request(&self, needed: Capability) -> NeededCapabilities {
        NeededCapabilities {
            capabilities: self.capabilities,
            needed,
        }
    }
}

/// A struct which can check that needed capability requirements are met.
pub struct NeededCapabilities {
    capabilities: Capability,
    needed: Capability,
}

impl NeededCapabilities {
    /// Checks that the requested capabilities are provided.
    pub fn ok(&self) -> Result<()> {
        if self.capabilities & self.needed != self.needed {
            Err(TransportError::MissingCapabilities(self.needed, self.capabilities).into())
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_capabilities_met() -> anyhow::Result<()> {
        let cap = Capabilities::new(Capability::UART | Capability::SPI);
        assert!(cap.request(Capability::UART).ok().is_ok());
        Ok(())
    }

    #[test]
    fn test_capabilities_not_met() -> anyhow::Result<()> {
        let cap = Capabilities::new(Capability::UART | Capability::SPI);
        assert!(cap.request(Capability::GPIO).ok().is_err());
        Ok(())
    }
}
