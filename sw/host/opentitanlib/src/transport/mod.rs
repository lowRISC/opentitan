// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use bitflags::bitflags;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use crate::bootstrap::BootstrapOptions;
use crate::io::emu::Emulator;
use crate::io::gpio::{GpioBitbanging, GpioMonitoring, GpioPin};
use crate::io::i2c::Bus;
use crate::io::jtag::{JtagChain, JtagParams};
use crate::io::spi::Target;
use crate::io::uart::Uart;

pub mod common;
pub mod ioexpander;

// Export custom error types
mod errors;
pub use errors::{TransportError, TransportInterfaceType};

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

    /// Returns a [`JtagChain`] implementation.
    fn jtag(&self, _opts: &JtagParams) -> Result<Box<dyn JtagChain + '_>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::Jtag).into())
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
    /// Returns a [`GpioBitbanging`] implementation, for timed and synchronized manipulation of
    /// multiple GPIO pins.
    fn gpio_bitbanging(&self) -> Result<Rc<dyn GpioBitbanging>> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::GpioBitbanging).into())
    }
    /// Returns a [`Emulator`] implementation.
    fn emulator(&self) -> Result<&dyn Emulator> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::Emulator).into())
    }

    /// Methods available only on FPGA implementations.
    fn fpga_ops(&self) -> Result<&dyn FpgaOps> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::FpgaOps).into())
    }

    /// Methods available only on Proxy implementation.
    fn proxy_ops(&self) -> Result<&dyn ProxyOps> {
        Err(TransportError::InvalidInterface(TransportInterfaceType::ProxyOps).into())
    }

    /// Invoke non-standard functionality of some Transport implementations.
    fn dispatch(&self, _action: &dyn Any) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Invoke the provided callback (preferably) without exclusive access.
    ///
    /// By default, ownership of `Transport` would imply exclusive access to the underlying device,
    /// and optimisation can be made assuming no other process would be simultaneously accessing.
    /// However for long running commands, such as `opentitantool console`, it may be desirable to
    /// relinquish exclusive access during such comamnd and only re-take exclusive access later.
    ///
    /// Transport that does not support such scenario may ignore such request and perform a no-op.
    fn relinquish_exclusive_access(&self, callback: Box<dyn FnOnce() + '_>) -> Result<()> {
        callback();
        Ok(())
    }
}

/// Methods available only on FPGA transports.
pub trait FpgaOps {
    fn load_bitstream(&self, bitstream: &[u8], progress: &dyn ProgressIndicator) -> Result<()>;

    fn clear_bitstream(&self) -> Result<()>;
}

/// Methods available only on the Proxy implementation of the Transport trait.
pub trait ProxyOps {
    /// Returns a string->string map containing user-defined aspects "provided" by the testbed
    /// setup.  For instance, whether a SPI flash chip is fitted in the socket, or whether pullup
    /// resistors are suitable for high-speed I2C.  Most of the time, this information will not
    /// come from the actual transport layer, but from the TransportWrapper above it.
    fn provides_map(&self) -> Result<HashMap<String, String>>;

    fn bootstrap(&self, options: &BootstrapOptions, payload: &[u8]) -> Result<()>;
    fn apply_pin_strapping(&self, strapping_name: &str) -> Result<()>;
    fn remove_pin_strapping(&self, strapping_name: &str) -> Result<()>;

    /// Applies the default transport init configuration expect with the specify strap applied.
    fn apply_default_configuration_with_strap(&self, strapping_name: &str) -> Result<()>;
}

/// Used by Transport implementations dealing with emulated OpenTitan
/// chips, allowing e.g. more efficient direct means of programming
/// emulated flash storage.  (As opposed to running an actual
/// bootloater on the emulated target, which would receive data via
/// SPI to be flashed.)
pub struct Bootstrap {
    pub image_path: PathBuf,
}

/// Some transports allow dynamically changing which pins are used for JTAG.
pub struct SetJtagPins {
    pub tclk: Option<Rc<dyn GpioPin>>,
    pub tms: Option<Rc<dyn GpioPin>>,
    pub tdi: Option<Rc<dyn GpioPin>>,
    pub tdo: Option<Rc<dyn GpioPin>>,
    pub trst: Option<Rc<dyn GpioPin>>,
}

pub trait ProgressIndicator {
    // Begins a new stage, indicating "size" of this stage in bytes.  `name` can be the empty
    // string, for instance if the operation has only a single stage.
    fn new_stage(&self, name: &str, total: usize);
    // Indicates how far towards the previously declared `total`.  Operation will be shown as
    // complete, once the parameter value to this method equals `total`.
    fn progress(&self, absolute: usize);
}

/// Command for Transport::dispatch().
pub struct UpdateFirmware<'a> {
    /// The firmware to load into the HyperDebug device, None means load an "official" newest
    /// release of the firmware for the particular debugger device, assuming that the `Transport`
    /// trait implementation knows how to download such.
    pub firmware: Option<Vec<u8>>,
    /// A progress function to provide user feedback, see details of the `Progress` struct.
    pub progress: Box<dyn ProgressIndicator + 'a>,
    /// Should updating be attempted, even if the current firmware version matches that of the
    /// image to be updated to.
    pub force: bool,
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
