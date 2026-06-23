// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Parameter structures for bootstrapping.

use std::time::Duration;

use clap::{Args, ValueEnum};
use humantime::parse_duration;
use serde::{Deserialize, Serialize};

use crate::io::spi::SpiParams;
use crate::io::uart::UartParams;

/// `BootstrapProtocol` describes the supported types of bootstrap.
/// The `Primitive` SPI protocol is used by OpenTitan during development.
/// The `Legacy` SPI protocol is used by previous generations of Google Titan-class chips.
/// The `LegacyRescue` UART protocol is used by previous generations of Google Titan-class chips.
/// The `Eeprom` SPI protocol is planned to be implemented for OpenTitan.
/// The 'Emulator' value indicates that this tool has a direct way
/// of communicating with the OpenTitan emulator, to replace the
/// contents of the emulated flash storage.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, ValueEnum)]
pub enum BootstrapProtocol {
    Primitive,
    Legacy,
    LegacyRescue,
    Eeprom,
    Emulator,
}

/// Options which control bootstrap behavior.
/// The meaning of each of these values depends on the specific bootstrap protocol being used.
#[derive(Clone, Debug, Args, Serialize, Deserialize)]
pub struct BootstrapOptions {
    #[command(flatten)]
    pub uart_params: UartParams,
    #[command(flatten)]
    pub spi_params: SpiParams,
    /// Bootstrap protocol to use.
    #[arg(short, long, value_enum, ignore_case = true, default_value = "eeprom")]
    pub protocol: BootstrapProtocol,
    /// Whether to reset target and clear UART RX buffer after bootstrap. For Chip Whisperer board only.
    #[arg(long)]
    pub clear_uart: Option<bool>,
    /// If set, keep the bootstrap strapping applied and do not perform the post-bootstrap reset
    /// sequence.
    #[arg(long)]
    pub leave_in_bootstrap: bool,
    /// If set, leave the reset signal asserted after completed bootstrapping.
    #[arg(long)]
    pub leave_in_reset: bool,
    /// Duration of the inter-frame delay.
    #[arg(long, value_parser = parse_duration)]
    pub inter_frame_delay: Option<Duration>,
    /// Duration of the flash-erase delay.
    #[arg(long, value_parser = parse_duration)]
    pub flash_erase_delay: Option<Duration>,
}
