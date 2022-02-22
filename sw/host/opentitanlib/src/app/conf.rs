// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Schema for configuration files, exact encoding json/xml to be worked out.

use crate::io::gpio::{PinMode, PullMode};

use serde::Deserialize;

/// Configuration of a particular GPIO pin.
#[derive(Deserialize, Clone, Debug)]
pub struct PinConfiguration {
    /// The user-visible name of the GPIO pin.
    pub name: String,
    /// The input/output mode of the GPIO pin.
    pub mode: Option<PinMode>,
    /// The default/initial level of the pin (true means high).
    pub level: Option<bool>,
    /// Whether the pin has pullup/down resistor enabled.
    pub pull_mode: Option<PullMode>,
    /// Name of a pin defined by the transport (or a lower level
    /// PinConfiguration).
    pub alias_of: Option<String>,
}

/// Configuration of a particular GPIO pin.
#[derive(Deserialize, Clone, Debug)]
pub struct StrappingConfiguration {
    /// The user-visible name of the strapping combination.
    pub name: String,
    /// List of GPIO pin configurations (the alias_of) field should not be used in these.
    #[serde(default)]
    pub pins: Vec<PinConfiguration>,
}

/// Parity configuration for UART communication.
#[derive(Deserialize, Clone, Debug)]
pub enum UartParity {
    None,
    Even,
    Odd,
    Mark,
    Space,
}

/// Stop bits configuration for UART communication.
#[derive(Deserialize, Clone, Debug)]
pub enum UartStopBits {
    Stop1,
    Stop1_5,
    Stop2,
}

/// Configuration of a particular UART port.
#[derive(Deserialize, Clone, Debug)]
pub struct UartConfiguration {
    /// The user-visible name of the UART.
    pub name: String,
    /// Data communication rate in bits/second.
    pub baudrate: Option<u32>,
    /// Parity configuration for UART communication.
    pub parity: Option<UartParity>,
    /// Stop bits configuration for UART communication.
    pub stopbits: Option<UartStopBits>,
    /// Name of the UART as defined by the transport.
    pub alias_of: Option<String>,
}

/// Configuration of a particular SPI controller port.
#[derive(Deserialize, Clone, Debug)]
pub struct SpiConfiguration {
    /// The user-visible name of the SPI controller port.
    pub name: String,
    /// Name of the SPI controller as defined by the transport.
    pub alias_of: Option<String>,
}

/// Representation of the complete and unresolved content of a single
/// confguration file.
#[derive(Deserialize, Clone, Debug)]
pub struct ConfigurationFile {
    /// Optional specification of transport backend, for which this
    /// configuration applies (to be implemented).
    pub interface: Option<String>,
    /// List of names of other configuration files to include recursively.
    #[serde(default)]
    pub includes: Vec<String>,
    /// List of GPIO pin configurations.
    #[serde(default)]
    pub pins: Vec<PinConfiguration>,
    /// List of named sets of additional GPIO pin configurations (pullup/pulldown).
    #[serde(default)]
    pub strappings: Vec<StrappingConfiguration>,
    /// List of UART configurations.
    #[serde(default)]
    pub uarts: Vec<UartConfiguration>,
}
