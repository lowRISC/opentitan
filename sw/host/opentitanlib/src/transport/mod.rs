// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use bitflags::bitflags;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::path::PathBuf;
use std::rc::Rc;

use crate::bootstrap::BootstrapOptions;
use crate::io::emu::Emulator;
use crate::io::gpio::{GpioMonitoring, GpioPin};
use crate::io::i2c::Bus;
use crate::io::spi::Target;
use crate::io::uart::Uart;

pub mod common;
pub mod cw310;
pub mod hyperdebug;
pub mod proxy;
pub mod ti50emulator;
pub mod ultradebug;
pub mod verilator;

// Export custom error types
mod errors;
pub use errors::{TransportError, TransportInterfaceType};

bitflags! {
    /// A bitmap of capabilities which may be provided by a transport.
    #[derive(Serialize, Deserialize)]
    pub struct Capability: u32 {
        const NONE = 0x00000000;
        const UART = 0x00000001;
        const SPI = 0x00000002;
        const GPIO = 0x00000004;
        const I2C = 0x00000008;
        const PROXY = 0x00000010;
        const EMULATOR = 0x00000020;
        const GPIO_MONITORING = 0x00000040; // Logic analyzer functionality
    }
}

/// A struct which represents what features a particular Transport instance supports.
#[derive(Serialize, Deserialize)]
pub struct Capabilities {
    capabilities: Capability,
}

impl Capabilities {
    /// Create a new Capabilities object representing a provider of
    /// capabilities specified by `cap`.
    fn new(cap: Capability) -> Self {
        Self { capabilities: cap }
    }

    fn add(&self, extra: Capability) -> Self {
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

/// A transport object is a factory for the low-level interfaces provided
/// by a given communications backend.
pub trait Transport {
    /// Returns a `Capabilities` object to check the capabilities of this
    /// transport object.
    fn capabilities(&self) -> Result<Capabilities>;

    /// Resets the transport to power-on condition.  That is, pin/uart/spi configuration reverts
    /// to default, ongoing operations are cancelled, etc.
    fn apply_default_configuration(&self) -> Result<()> {
        Ok(())
    }

    /// Returns a SPI [`Target`] implementation.
    fn spi(&self, _instance: &str) -> Result<Rc<dyn Target>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::Spi).into())
    }
    /// Returns a I2C [`Bus`] implementation.
    fn i2c(&self, _instance: &str) -> Result<Rc<dyn Bus>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::I2c).into())
    }
    /// Returns a [`Uart`] implementation.
    fn uart(&self, _instance: &str) -> Result<Rc<dyn Uart>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::Uart).into())
    }
    /// Returns a [`GpioPin`] implementation.
    fn gpio_pin(&self, _instance: &str) -> Result<Rc<dyn GpioPin>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::Gpio).into())
    }
    /// Returns a [`GpioMonitoring`] implementation, for logic analyzer functionality.
    fn gpio_monitoring(&self) -> Result<Rc<dyn GpioMonitoring>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::GpioMonitoring).into())
    }
    /// Returns a [`Emulator`] implementation.
    fn emulator(&self) -> Result<Rc<dyn Emulator>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::Emulator).into())
    }

    /// Methods available only on Proxy implementation.
    fn proxy_ops(&self) -> Result<Rc<dyn ProxyOps>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::ProxyOps).into())
    }

    /// Invoke non-standard functionality of some Transport implementations.
    fn dispatch(&self, _action: &dyn Any) -> Result<Option<Box<dyn serde_annotate::Annotate>>> {
        Err(TransportError::UnsupportedOperation.into())
    }
}

/// Methods available only on the Proxy implementation of the Transport trait.
pub trait ProxyOps {
    fn bootstrap(&self, options: &BootstrapOptions, payload: &[u8]) -> Result<()>;
    fn apply_pin_strapping(&self, strapping_name: &str) -> Result<()>;
    fn remove_pin_strapping(&self, strapping_name: &str) -> Result<()>;
}

/// Used by Transport implementations dealing with emulated OpenTitan
/// chips, allowing e.g. more efficient direct means of programming
/// emulated flash storage.  (As opposed to running an actual
/// bootloater on the emulated target, which would receive data via
/// SPI to be flashed.)
pub struct Bootstrap {
    pub image_path: PathBuf,
}

pub enum Progress {
    /// Declares that a stage of the operation is starting, giving the total number of bytes to be
    /// processed in this stage.  If only a single stage, `name` may be the empty string.
    Stage { name: String, total: u32 },
    /// Informs about progress within the current state, `pos` is absolute number of bytes so far.
    Progress { pos: u32 },
}

/// Command for Transport::dispatch().
pub struct UpdateFirmware<'a> {
    /// The firmware to load into the HyperDebug device, None means load an "official" newest
    /// release of the firmware for the particular debugger device, assuming that the `Transport`
    /// trait implementation knows how to download such.
    pub firmware: Option<Vec<u8>>,
    /// A progress function to provide user feedback, see details of the `Progress` struct.
    pub progress: Option<Box<dyn Fn(Progress) + 'a>>,
}

/// An `EmptyTransport` provides no communications backend.
pub struct EmptyTransport;

impl Transport for EmptyTransport {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(Capability::NONE))
    }
}

#[cfg(test)]
pub mod tests {
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
