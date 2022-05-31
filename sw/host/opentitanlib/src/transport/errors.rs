// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::Capability;
use crate::impl_serializable_error;

/// Contains all the errors that any method on the `Transport` trait could generate.  This
/// struct is serializable, such that it can be transmitted across a network for instance as
/// part of the session proxy functionality.
#[derive(Error, Debug, Serialize, Deserialize)]
pub enum TransportError {
    #[error("USB device did not match")]
    NoMatch,
    #[error("Found no USB device")]
    NoDevice,
    #[error("Found multiple USB devices, use --serial")]
    MultipleDevices,
    #[error("USB error: {0}")]
    UsbGenericError(String),
    #[error("Error opening USB device: {0}")]
    UsbOpenError(String),
    #[error("Transport does not support {0:?}")]
    InvalidInterface(TransportInterfaceType),
    #[error("Transport does not support {0:?} instance {1}")]
    InvalidInstance(TransportInterfaceType, String),
    #[error("Encountered non-unicode device path")]
    UnicodePathError,
    #[error("Error opening {0}: {1}")]
    OpenError(String, String),
    #[error("Error reading from {0}: {1}")]
    ReadError(String, String),
    #[error("FPGA programming failed: {0}")]
    FpgaProgramFailed(String),
    #[error("PLL programming failed: {0}")]
    PllProgramFailed(String),
    #[error("Invalid pin strapping name \"{0}\"")]
    InvalidStrappingName(String),
    #[error("Transport does not support the requested operation")]
    UnsupportedOperation,
    #[error("Error communicating with FTDI: {0}")]
    FtdiError(String),
    #[error("Error communicating with debugger: {0}")]
    CommunicationError(String),
    #[error("Proxy unable to resolve `{0}`: {1}")]
    ProxyLookupError(String, String),
    #[error("Proxy unable to connect to `{0}`: {1}")]
    ProxyConnectError(String, String),
    #[error("Requested capabilities {0:?}, but capabilities {1:?} are supplied")]
    MissingCapabilities(Capability, Capability),
}
impl_serializable_error!(TransportError);

/// Enum value used by `TransportError::InvalidInstance`.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub enum TransportInterfaceType {
    Gpio,
    Uart,
    Spi,
    I2c,
    Emulator,
    ProxyOps,
}
