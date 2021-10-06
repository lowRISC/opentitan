// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Useful modules for OpenTitanTool application development.
pub mod command;
pub mod conf;

use crate::io::gpio::GpioPin;
use crate::io::spi::Target;
use crate::io::uart::Uart;

use anyhow::Result;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

// This is the structure to be passed to each Command implementation,
// replacing the "bare" Transport argument.  The fields other than
// transport will have been computed from a number ConfigurationFiles.
pub struct TransportWrapper {
    transport: RefCell<Box<dyn crate::transport::Transport>>,
    pub pin_map: HashMap<String, String>,
    pub uart_map: HashMap<String, String>,
    pub spi_map: HashMap<String, String>,
    pub flash_map: HashMap<String, conf::FlashConfiguration>,
}

impl TransportWrapper {
    pub fn new(transport: Box<dyn crate::transport::Transport>) -> Self {
        Self {
            transport: RefCell::new(transport),
            pin_map: HashMap::new(),
            uart_map: HashMap::new(),
            spi_map: HashMap::new(),
            flash_map: HashMap::new(),
        }
    }

    /// Returns a `Capabilities` object to check the capabilities of this
    /// transport object.
    pub fn capabilities(&self) -> crate::transport::Capabilities {
        self.transport.borrow().capabilities()
    }

    /// Returns a SPI [`Target`] implementation.
    pub fn spi(&self, name: &str) -> Result<Rc<dyn Target>> {
        self.transport.borrow().spi(Self::map_name(&self.spi_map, name).as_str())
    }

    /// Returns a [`Uart`] implementation.
    pub fn uart(&self, name: &str) -> Result<Rc<dyn Uart>> {
        self.transport.borrow().uart(Self::map_name(&self.uart_map, name).as_str())
    }

    /// Returns a [`GpioPin`] implementation.
    pub fn gpio_pin(&self, name: &str) -> Result<Rc<dyn GpioPin>> {
        self.transport.borrow().gpio_pin(Self::map_name(&self.pin_map, name).as_str())
    }

    /// Programs a bitstream into an FPGA.
    pub fn fpga_program(&self, bitstream: &[u8]) -> Result<()> {
        self.transport.borrow().fpga_program(bitstream)
    }
    
    /// Given an pin/uart/spi port name, if the name is a known alias,
    /// return the underlying name/number, otherwise return the string
    /// as is.
    fn map_name(
        map: &HashMap<String, String>,
        name: &str
    ) -> String {
        let name = name.to_uppercase();
        // TODO(#8769): Support multi-level aliasing, either by
        // flattening after parsing all files, or by repeated lookup
        // here.
        map.get(&name).cloned().unwrap_or(name)
    }

    pub fn add_configuration_file(&mut self, file: conf::ConfigurationFile) -> Result<()> {
        // Merge content of configuration file into pin_map and other
        // members.
        for pin_conf in file.pins {
            if let Some(alias_of) = pin_conf.alias_of {
                self.pin_map.insert(pin_conf.name.to_uppercase(), alias_of);
            }
            // TODO(#8769): Apply input / open drain / push pull
            // configuration to the pin.
        }
        for uart_conf in file.uarts {
            if let Some(alias_of) = uart_conf.alias_of {
                self.uart_map.insert(uart_conf.name.to_uppercase(), alias_of);
            }
            // TODO(#8769): Record baud / parity configration for later
            // use when opening uart.
        }
        for flash_conf in file.flash {
            self.flash_map.insert(flash_conf.name.clone(), flash_conf.clone());
        }
        Ok(())
    }
}
