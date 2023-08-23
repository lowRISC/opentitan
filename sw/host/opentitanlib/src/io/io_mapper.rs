// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::{gpio, i2c, spi};
use anyhow::Result;
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

use crate::io::gpio::GpioError;
use crate::transport::{TransportError, TransportInterfaceType};

#[derive(Default, Clone)]
pub struct AliasMapper {
    map: HashMap<String, String>,
}

/// Given an pin/uart/spi/i2c port name, if the name is a known alias, return the underlying
/// name/number, otherwise return the string as is.
impl AliasMapper {
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the `name` itself if it is not mapped.
    pub fn resolve(&self, name: &str) -> String {
        let name = name.to_uppercase();
        match self.map.get(&name) {
            Some(v) => {
                if v.eq(&name) {
                    name
                } else {
                    self.resolve(v)
                }
            }
            None => name,
        }
    }

    /// Return None if the name is not mapped.
    pub fn try_resolve(&self, name: &str) -> Option<&String> {
        if let Some(name) = self.map.get(name) {
            return Some(name);
        }
        let name = name.to_uppercase();
        self.map.get(&name)
    }
}

impl Deref for AliasMapper {
    type Target = HashMap<String, String>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl DerefMut for AliasMapper {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

#[derive(Default)]
pub struct IoMapper {
    pub pin_map: AliasMapper,
    pub uart_map: AliasMapper,
    pub i2c_map: AliasMapper,
    pub pin_conf_map: HashMap<String, gpio::PinConfiguration>,
    pub spi_conf_map: HashMap<String, spi::SpiConfiguration>,
    pub i2c_conf_map: HashMap<String, i2c::I2cConfiguration>,
    pub strapping_conf_map: HashMap<String, HashMap<String, gpio::PinConfiguration>>,
}

impl IoMapper {
    pub fn resolve_pin(&self, name: &str) -> String {
        self.pin_map.resolve(name)
    }

    pub fn pin_config(&self, name: &str) -> Result<&gpio::PinConfiguration> {
        let name = self.resolve_pin(name);
        Ok(self
            .pin_conf_map
            .get(&name)
            .ok_or(GpioError::InvalidPinName(name.to_string()))?)
    }

    pub fn pin_level(&self, name: &str) -> Result<bool> {
        let name = self.resolve_pin(name);
        Ok(self.pin_config(&name)?.level.unwrap_or(false))
    }

    pub fn pin_mode(&self, name: &str) -> Result<gpio::PinMode> {
        let name = self.resolve_pin(name);
        Ok(self
            .pin_config(&name)?
            .mode
            .unwrap_or(gpio::PinMode::PushPull))
    }

    pub fn list_gpio_pins_alias(&self) -> impl Iterator<Item = &String> {
        self.pin_map.keys()
    }

    pub fn list_gpio_pins(&self) -> impl Iterator<Item = &String> {
        self.pin_map.values()
    }

    pub fn spi_config(&self, name: &str) -> Result<&spi::SpiConfiguration> {
        self.spi_conf_map.get(name).ok_or(
            TransportError::InvalidInstance(TransportInterfaceType::Spi, name.to_string()).into(),
        )
    }

    pub fn resolve_spi(&self, name: &str) -> Result<&String> {
        Ok(&self.spi_config(name)?.underlying_instance)
    }

    pub fn resolve_i2c(&self, name: &str) -> Result<&String> {
        self.i2c_map.try_resolve(name).ok_or(
            TransportError::InvalidInstance(TransportInterfaceType::I2c, name.to_string()).into(),
        )
    }

    pub fn resolve_uart(&self, name: &str) -> String {
        self.uart_map.resolve(name)
    }

    pub fn strapping_conf(&self, name: &str) -> Result<&HashMap<String, gpio::PinConfiguration>> {
        self.strapping_conf_map
            .get(name)
            .ok_or(GpioError::InvalidPinName(name.to_string()).into())
    }
}
