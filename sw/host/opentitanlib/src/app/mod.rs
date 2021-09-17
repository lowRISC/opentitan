// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Useful modules for OpenTitanTool application development.
pub mod command;
pub mod conf;

use anyhow::Result;
use std::collections::HashMap;
use thiserror::Error;

// This is the structure to be passed to each Command implementation,
// replacing the "bare" Transport argument.  The fields other than
// transport will have been computed from a number ConfigurationFiles.
pub struct TargetEnvironment {
    pub transport: std::cell::RefCell<Box<dyn crate::transport::Transport>>,
    pub pin_map: HashMap<String, u32>,
    pub _uart_map: HashMap<String, u32>,
    pub _spi_map: HashMap<String, u32>,
    pub flash_map: HashMap<String, conf::FlashConfiguration>,
}

impl TargetEnvironment {
    pub fn new(transport: Box<dyn crate::transport::Transport>) -> Self {
        let mut result = Self {
            transport: std::cell::RefCell::new(transport),
            pin_map: HashMap::new(),
            _uart_map: HashMap::new(),
            _spi_map: HashMap::new(),
            flash_map: HashMap::new(),
        };
        // TODO(jbk): Load symbolic names of pins as advertised by the
        // transport itself into pin_map and other members, for now
        // these hard-coded values are appropriate for UltraDebug.
        result.pin_map.insert("5".to_string(), 5);
        result.pin_map.insert("6".to_string(), 6);
        result.pin_map.insert("UD_RESET_B".to_string(), 5);
        result.pin_map.insert("UD_BOOTSTRAP".to_string(), 6);
        result
    }

    pub fn add_configuration_file(&mut self, file: conf::ConfigurationFile) -> Result<()> {
        // Merge content of configuration file into pin_map and other
        // members.
        for pin_conf in file.pins {
            let pin = *self.pin_map.get(&pin_conf.alias_of)
                .ok_or(Error::InvalidPin(pin_conf.alias_of.clone()))?;
            self.pin_map.insert(pin_conf.name, pin);
            // TODO(jbk): Apply input / open drain / push pull
            // configuration to the pin.
        }
        for flash_conf in file.flash {
            self.flash_map.insert(flash_conf.name.clone(), flash_conf.clone());
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("Invalid pin name: {0}")]
    InvalidPin(String),
}
