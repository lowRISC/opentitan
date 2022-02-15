// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Useful modules for OpenTitanTool application development.
pub mod command;
pub mod conf;

use crate::io::gpio::{GpioPin, PinMode, PullMode};
use crate::io::i2c::Bus;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{Result, Transport, TransportError};

use erased_serde::Serialize;
use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Default)]
pub struct PinConfiguration {
    /// The input/output mode of the GPIO pin.
    pub mode: Option<PinMode>,
    /// The default/initial level of the pin (true means high).
    pub level: Option<bool>,
    /// Whether the pin has pullup/down resistor enabled.
    pub pull_mode: Option<PullMode>,
}

// This is the structure to be passed to each Command implementation,
// replacing the "bare" Transport argument.  The fields other than
// transport will have been computed from a number ConfigurationFiles.
pub struct TransportWrapper {
    transport: RefCell<Box<dyn Transport>>,
    pin_map: HashMap<String, String>,
    uart_map: HashMap<String, String>,
    spi_map: HashMap<String, String>,
    i2c_map: HashMap<String, String>,
    flash_map: HashMap<String, conf::FlashConfiguration>,
    pin_conf_map: HashMap<String, PinConfiguration>,
    strapping_conf_map: HashMap<String, HashMap<String, PinConfiguration>>,
}

impl TransportWrapper {
    pub fn new(transport: Box<dyn crate::transport::Transport>) -> Self {
        Self {
            transport: RefCell::new(transport),
            pin_map: HashMap::new(),
            uart_map: HashMap::new(),
            spi_map: HashMap::new(),
            i2c_map: HashMap::new(),
            flash_map: HashMap::new(),
            pin_conf_map: HashMap::new(),
            strapping_conf_map: HashMap::new(),
        }
    }

    /// Returns a `Capabilities` object to check the capabilities of this
    /// transport object.
    pub fn capabilities(&self) -> crate::transport::Capabilities {
        self.transport.borrow().capabilities()
    }

    /// Returns a SPI [`Target`] implementation.
    pub fn spi(&self, name: &str) -> Result<Rc<dyn Target>> {
        self.transport
            .borrow()
            .spi(Self::map_name(&self.spi_map, name).as_str())
    }

    /// Returns a I2C [`Bus`] implementation.
    pub fn i2c(&self, name: &str) -> Result<Rc<dyn Bus>> {
        self.transport
            .borrow()
            .i2c(Self::map_name(&self.i2c_map, name).as_str())
    }

    /// Returns a [`Uart`] implementation.
    pub fn uart(&self, name: &str) -> Result<Rc<dyn Uart>> {
        self.transport
            .borrow()
            .uart(Self::map_name(&self.uart_map, name).as_str())
    }

    /// Returns a [`GpioPin`] implementation.
    pub fn gpio_pin(&self, name: &str) -> Result<Rc<dyn GpioPin>> {
        self.transport
            .borrow()
            .gpio_pin(Self::map_name(&self.pin_map, name).as_str())
    }

    /// Invoke non-standard functionality of some Transport implementations.
    pub fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn Serialize>>> {
        self.transport.borrow().dispatch(action)
    }

    /// Given an pin/uart/spi/i2c port name, if the name is a known
    /// alias, return the underlying name/number, otherwise return the
    /// string as is.
    fn map_name(map: &HashMap<String, String>, name: &str) -> String {
        let name = name.to_uppercase();
        // TODO(#8769): Support multi-level aliasing, either by
        // flattening after parsing all files, or by repeated lookup
        // here.
        map.get(&name).cloned().unwrap_or(name)
    }

    /// Apply given configuration to a single pins.
    fn apply_pin_configuration(&self, name: &str, conf: &PinConfiguration) -> Result<()> {
        let pin = self.gpio_pin(name)?;
        if let Some(pin_mode) = conf.mode {
            pin.set_mode(pin_mode)?;
        }
        if let Some(pull_mode) = conf.pull_mode {
            pin.set_pull_mode(pull_mode)?;
        }
        if let Some(level) = conf.level {
            pin.write(level)?;
        }
        Ok(())
    }

    /// Apply given configuration to a all the given pins.
    fn apply_pin_configurations(&self, conf_map: &HashMap<String, PinConfiguration>) -> Result<()> {
        for (name, conf) in conf_map {
            self.apply_pin_configuration(name, conf)?
        }
        Ok(())
    }

    /// Configure all pins as input/output, pullup, etc. as declared in configuration files.
    pub fn apply_default_pin_configurations(&self) -> Result<()> {
        self.apply_pin_configurations(&self.pin_conf_map)
    }

    /// Configure a specific set of pins as strong/weak pullup/pulldown as declared in
    /// configuration files under a given strapping name.
    pub fn apply_pin_strapping(&self, strapping_name: &str) -> Result<()> {
        if let Some(strapping_conf_map) = self.strapping_conf_map.get(strapping_name) {
            self.apply_pin_configurations(&strapping_conf_map)
        } else {
            Err(TransportError::InvalidStrappingName(strapping_name.to_string()))
        }
    }

    /// Return the set of pins affected by the given strapping to their "default" (un-strapped)
    /// configuration, that is, to the level declared in the "pins" section of configuration
    /// files, outside of any "strappings" section.
    pub fn remove_pin_strapping(&self, strapping_name: &str) -> Result<()> {
        if let Some(strapping_conf_map) = self.strapping_conf_map.get(strapping_name) {
            for (pin_name, _conf) in strapping_conf_map {
                if let Some(default_pin_conf) = self.pin_conf_map.get(pin_name) {
                    self.apply_pin_configuration(&pin_name, &default_pin_conf)?;
                }
            }
            Ok(())
        } else {
            Err(TransportError::InvalidStrappingName(strapping_name.to_string()))
        }
    }

    /// Records the default configuration of a pin, possibly partially overriding previous
    /// configuration.  (E.g. base level configuration files declares a pin as push/pull with a
    /// low level.  A higher level configuration file (which referred to the former in an
    /// include directive) then declares a high level without mentioning input/output/open-drain
    /// mode.  The latter will be processed last, and override just the "level" field, while
    /// leaving the "pin_mode" field unchanged.
    fn record_pin_conf(
        pin_map: &HashMap<String, String>,
        pin_conf_map: &mut HashMap<String, PinConfiguration>,
        pin_conf: &conf::PinConfiguration,
    ) {
        if let Some(pin_mode) = pin_conf.mode {
            pin_conf_map
                .entry(Self::map_name(pin_map, &pin_conf.name))
                .or_insert(Default::default())
                .mode = Some(pin_mode);
        }
        if let Some(pull_mode) = pin_conf.pull_mode {
            pin_conf_map
                .entry(Self::map_name(pin_map, &pin_conf.name))
                .or_insert(Default::default())
                .pull_mode = Some(pull_mode);
        }
        if let Some(level) = pin_conf.level {
            pin_conf_map
                .entry(Self::map_name(pin_map, &pin_conf.name))
                .or_insert(Default::default())
                .level = Some(level);
        }
    }

    pub fn add_configuration_file(&mut self, file: conf::ConfigurationFile) -> anyhow::Result<()> {
        // Merge content of configuration file into pin_map and other
        // members.
        for pin_conf in file.pins {
            if let Some(alias_of) = &pin_conf.alias_of {
                self.pin_map
                    .insert(pin_conf.name.to_uppercase(), alias_of.clone());
            }
            // Record default input / open drain / push pull configuration to the pin.
            Self::record_pin_conf(&self.pin_map, &mut self.pin_conf_map, &pin_conf);
        }
        for strapping_conf in file.strappings {
            let mut strapping_pin_map = HashMap::new();
            for pin_conf in strapping_conf.pins {
                Self::record_pin_conf(&self.pin_map, &mut strapping_pin_map, &pin_conf);
            }
            self.strapping_conf_map
                .insert(strapping_conf.name.to_uppercase(), strapping_pin_map);
        }
        for uart_conf in file.uarts {
            if let Some(alias_of) = &uart_conf.alias_of {
                self.uart_map
                    .insert(uart_conf.name.to_uppercase(), alias_of.clone());
            }
            // TODO(#8769): Record baud / parity configration for later
            // use when opening uart.
        }
        for flash_conf in file.flash {
            self.flash_map
                .insert(flash_conf.name.clone(), flash_conf.clone());
        }
        Ok(())
    }
}
