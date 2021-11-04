// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use std::cell::RefCell;
use std::rc::Rc;

use crate::io::gpio::GpioPin;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{Capabilities, Capability, Transport};

#[derive(Default)]
pub struct HostEmulation {
    pub port: u16,
    _inner: RefCell<Inner>,
}

/// Internal mutable state of the HostEmulation struct.
#[derive(Default)]
struct Inner {
}

impl HostEmulation {
    pub const DEFAULT_PORT: u16 = 5555;

    /// Create a new `HostEmulation` struct, optionally specifying the
    /// port to connect to.
    pub fn new(port: Option<u16>) -> Self {
        Self {
            port: port.unwrap_or(Self::DEFAULT_PORT),
            ..Default::default()
        }
    }
}

impl Transport for HostEmulation {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(Capability::UART | Capability::GPIO | Capability::SPI)
    }

    fn uart(&self, _instance: &str) -> Result<Rc<dyn Uart>> {
        unimplemented!();
    }

    fn gpio_pin(&self, _instance: &str) -> Result<Rc<dyn GpioPin>> {
        unimplemented!();
    }

    fn spi(&self, _instance: &str) -> Result<Rc<dyn Target>> {
        unimplemented!();
    }
}
