// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use thiserror::Error;

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
    #[error("Invalid pin strapping name \"{0}\"")]
    InvalidStrappingName(String),
    #[error("Transport does not support the requested operation")]
    UnsupportedOperation,
    #[error("Error communicating with FTDI: {0}")]
    FtdiError(String),
    #[error("Error communicating with debugger: {0}")]
    CommunicationError(String),

    // Include sub-enums for the various sub-traits of Tranport.
    #[error("GPIO error: {0}")]
    GpioError(#[from] crate::io::gpio::GpioError),
    #[error("UART error: {0}")]
    UartError(#[from] crate::io::uart::UartError),
    #[error("SPI error: {0}")]
    SpiError(#[from] crate::io::spi::SpiError),
    #[error("SPI error: {0}")]
    I2cError(#[from] crate::io::i2c::I2cError),
}

/// Enum value used by `TransportError::InvalidInstance`.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub enum TransportInterfaceType {
    Gpio,
    Uart,
    Spi,
    I2c,
}

/// Return type to be used in `Transport` methods.
pub type Result<T> = anyhow::Result<T, TransportError>;

/// Convenience macro to be used in implementations of `Transport`.
#[macro_export]
macro_rules! bail {
    ($err:expr $(,)?) => {
        return Err($err.into());
    };
}

/// Convenience macro to be used in implementations of `Transport`.
#[macro_export]
macro_rules! ensure {
    ($cond:expr, $err:expr $(,)?) => {
        if !$cond {
            return Err($err.into());
        }
    };
}

/// Function for conveniently wrapping (the flat string representation of) an anyhow::Error in a
/// TransportError.
///
/// Example usage:
/// serialport::available_ports().wrap(UartError::EnumerationError)?;
pub trait WrapInTransportError<T> {
    fn wrap<S: Into<TransportError>>(self, kind: impl FnOnce(String) -> S) -> Result<T>;
}

impl<T, E: ToString> WrapInTransportError<T> for anyhow::Result<T, E> {
    fn wrap<S: Into<TransportError>>(self, kind: impl FnOnce(String) -> S) -> Result<T> {
        self.map_err(|e| kind(e.to_string()).into())
    }
}
