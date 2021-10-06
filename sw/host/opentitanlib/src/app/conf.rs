// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Schema for configuration files, exact encoding json/xml to be worked out.

use serde::Deserialize;

/// Overall operating mode of a single GPIO pin.
#[derive(Deserialize, Clone, Debug)]
pub enum PinMode {
    Input,
    PushPull,
    OpenDrain,
}

/// Configuration of passive pullup/down for a single GPIO pin.
#[derive(Deserialize, Clone, Debug)]
pub enum PullMode {
    None,
    PullUp,
    PullDown,
}

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

#[derive(Deserialize, Clone, Debug, PartialEq, Eq)]
pub enum FlashAddressMode {
    Mode3b,
    Mode4b,
}


/// Chip programmed via an EEPROM-like SPI protocol.
#[derive(Deserialize, Clone, Debug)]
pub struct SpiEeprom {
    size: u32,
    erase_block_size: u32,
    erase_opcode: u8,
    program_block_size: u32,
    address_mode: FlashAddressMode,
    /// Name of spi bus as defined by transport.
    spi_bus: String,
    // Possibly add more fields to declare SPI mode/speed
}

/// Temporary measure to allow external program to implement SPI protocol.
#[derive(Deserialize, Clone, Debug)]
pub struct SpiExternalDriver {
    command: String,
    /// Name of spi bus as defined by transport.
    spi_bus: String,
    // Possibly add more fields to declare SPI mode/speed
}

/// Defines the protocol used by a particular programmable chip.
#[derive(Deserialize, Clone, Debug)]
pub enum FlashDriver {
    /// Chip programmed via an EEPROM-like SPI protocol.
    SpiEeprom(SpiEeprom),
    /// Temporary measure to allow external program to implement SPI protocol.
    SpiExternalDriver(SpiExternalDriver)
}

/// Defines the way to reach and program flash storage.
#[derive(Deserialize, Clone, Debug)]
pub struct FlashConfiguration {
    /// The user-visible name of the flash storage.
    pub name: String,
    /// Name of the reset pin to be used.
    pub reset_pin: String,
    /// Name of the bootloade pin to be held high during reset.
    pub bootloader_pin: Option<String>,
    /// Declaration of the particular flashing protocol to be used.
    pub driver: FlashDriver,
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
    /// List of UART configurations.
    #[serde(default)]
    pub uarts: Vec<UartConfiguration>,
    /// List of configurations of programmable storage.
    #[serde(default)]
    pub flash: Vec<FlashConfiguration>,
}

