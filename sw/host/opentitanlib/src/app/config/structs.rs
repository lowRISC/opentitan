// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Schema for configuration files, exact encoding json/xml to be worked out.

use crate::io::gpio::{PinMode, PullMode};
use crate::io::spi::TransferMode;

use serde::Deserialize;
use std::collections::HashMap;

/// Configuration of a particular GPIO pin.
#[derive(Deserialize, Clone, Debug)]
pub struct PinConfiguration {
    /// The user-visible name of the GPIO pin.
    pub name: String,
    /// The input/output mode of the GPIO pin.
    pub mode: Option<PinMode>,
    /// The default/initial level of the pin (true means high), has effect only in `PushPull` and
    /// `OpenDrain` modes.
    pub level: Option<bool>,
    /// Whether the pin has pullup/down resistor enabled.
    pub pull_mode: Option<PullMode>,
    /// The default/initial analog level of the pin in Volts, has effect only in `AnalogOutput`
    /// mode.
    pub volts: Option<f32>,
    /// If present, the name given by the first member of this struct is to be an alias of the pin
    /// named in this field, (which may by defined by the transport natively, or through alias in
    /// nother PinConfiguration).  This field is mutually exclusive with `on_io_expander`.
    pub alias_of: Option<String>,
    /// If true, value of this pins will be inverted both at reading and writing.
    pub invert: Option<bool>,
    /// If present, this pin is not natively supported by the transport, but is to be accessed
    /// through an IO expander.  This field is mutually exclusive with `alias_of`.
    pub on_io_expander: Option<IoExpanderPin>,
}

/// Declaration of a name of an IO expander and pin number on it.
#[derive(Deserialize, Clone, Debug)]
pub struct IoExpanderPin {
    pub io_expander: String,
    pub pin_no: u32,
}

/// Declaration of an IO expander.  Its name, how to reach it, and which protocol driver to use.
#[derive(Deserialize, Clone, Debug)]
pub struct IoExpander {
    /// Name used to refer to this IO expander.
    pub name: String,
    /// Identifier of the driver to use.
    pub driver: IoExpanderDriver,
    /// I2C bus on which this IO expander sits (if the driver uses I2C).
    pub i2c_bus: Option<String>,
    /// I2C address of this IO expander sits (if the driver uses I2C).
    pub i2c_address: Option<u8>,
    /// Optional gpio strapping for MUXing the bus from the transport to this IO expander.
    pub mux_strapping: Option<String>,
}

/// Identifier of the driver/protocol uses by an IO expander.
#[derive(Deserialize, Clone, Debug)]
pub enum IoExpanderDriver {
    Sx1503,
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
#[derive(Default, Deserialize, Clone, Debug)]
pub struct SpiConfiguration {
    /// The user-visible name of the SPI controller port.
    pub name: String,
    /// SPI transfer mode to use with this target.
    /// See <https://en.wikipedia.org/wiki/Serial_Peripheral_Interface#Clock_polarity_and_phase>
    /// for details about SPI transfer modes.
    pub mode: Option<TransferMode>,
    /// Number of bits in each SPI transmissiong "word".
    pub bits_per_word: Option<u32>,
    /// Data communication rate in bits/second.
    pub bits_per_sec: Option<u32>,
    /// Which GPIO pin should be used for chip select.
    pub chip_select: Option<String>,
    /// Name of the SPI controller as defined by the transport.
    pub alias_of: Option<String>,
}

/// Configuration of a particular I2C bus.
#[derive(Default, Deserialize, Clone, Debug)]
pub struct I2cConfiguration {
    /// The user-visible name of the I2C bus.
    pub name: String,
    /// I2C address of the "default" device on the bus.
    pub address: Option<u8>,
    /// Data communication rate in bits/second.
    pub bits_per_sec: Option<u32>,
    /// Name of the I2C bus as defined by the transport.
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
    /// List of user-defined features "provided" by the testing setup using this file.
    #[serde(default)]
    pub provides: HashMap<String, String>,
    /// List of user-defined features which must be "provided" by the testing setup (through other
    /// configuration files), in order for it to make sense to use this file.
    #[serde(default)]
    pub requires: HashMap<String, String>,
    /// List of GPIO pin configurations.
    #[serde(default)]
    pub pins: Vec<PinConfiguration>,
    /// List of named sets of additional GPIO pin configurations (pullup/pulldown).
    #[serde(default)]
    pub strappings: Vec<StrappingConfiguration>,
    /// List of SPI port configurations.
    #[serde(default)]
    pub spi: Vec<SpiConfiguration>,
    /// List of I2C port configurations.
    #[serde(default)]
    pub i2c: Vec<I2cConfiguration>,
    /// List of UART port configurations.
    #[serde(default)]
    pub uarts: Vec<UartConfiguration>,
    /// List of IO expander chips.
    #[serde(default)]
    pub io_expanders: Vec<IoExpander>,
}
