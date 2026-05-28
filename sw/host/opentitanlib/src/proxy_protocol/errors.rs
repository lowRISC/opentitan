// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use opentitanlib_core::io::SerializableError;

/// `SerializedError` is the wire form of errors that can be sent through the proxy.
#[derive(serde::Serialize, serde::Deserialize, Debug)]
pub struct SerializedError {
    pub description: String,
    pub backtrace: String,
    pub error: Option<Box<dyn SerializableError>>,
}

// Helper macro for building the `From` implementation that converts
// native error types into their serialized form. This is a recursive
// macro.
macro_rules! to_serialized_error {
    // This is the terminal state for this macro: only one type to convert.
    // Parameters:
    //   error - The error object.
    //   msg - The error message (e.g. `to_string()`).
    //   bt - The error backtrace.
    //   box - A function which can box the error if needed.
    //   t - The error type to convert.
    ($error:expr, $msg:expr, $bt:expr, $box:expr, $t:ty $(,)?) => {{
        match $error.downcast::<$t>() {
            Ok(e) => return SerializedError {
                description: $msg,
                backtrace: $bt,
                error: Some($box(e)),
            },

            Err(_) => return SerializedError {
                description: $msg,
                backtrace: $bt,
                error: None,
            },
        }
    }};

    // This is the non-terminal state for this macro: many types to convert.
    // Parameters:
    //   error - The error object.
    //   msg - The error message (e.g. `to_string()`).
    //   bt - The error backtrace.
    //   box - A function which can box the error if needed.
    //   t:ts - The error types to convert.
    ($error:expr, $msg:expr, $bt:expr, $box:expr, $t:ty, $($ts:ty),+ $(,)?) => {{
        let e2 = match $error.downcast::<$t>() {
            Ok(e) => return SerializedError {
                description: $msg,
                backtrace: $bt,
                error: Some($box(e)),
            },
            Err(e) => e,
        };
        to_serialized_error!(e2, $msg, $bt, $box, $($ts,)*);
    }};
}

/// Converts a `SerializedError` back into a real error type.
impl From<SerializedError> for anyhow::Error {
    fn from(ser: SerializedError) -> anyhow::Error {
        let error = if let Some(error) = ser.error {
            error.as_anyhow_error()
        } else {
            anyhow::Error::msg(ser.description)
        };
        if ser.backtrace == "<disabled>" {
            error
        } else {
            error.context(format!("Server Error.\nRemote {}", ser.backtrace))
        }
    }
}

/// Converts any error into a `SerializedError`.
impl From<anyhow::Error> for SerializedError {
    fn from(error: anyhow::Error) -> SerializedError {
        let msg = error.to_string();
        let bt = format!("{:#?}", error.backtrace());
        to_serialized_error!(
            error,
            msg,
            bt,
            Box::new,
            opentitanlib_core::io::console::ConsoleError,
            opentitanlib_core::io::emu::EmuError,
            opentitanlib_core::io::gpio::GpioError,
            opentitanlib_core::io::i2c::I2cError,
            opentitanlib_core::io::jtag::JtagError,
            opentitanlib_core::io::spi::SpiError,
            opentitanlib_core::io::uart::UartError,
            opentitanlib_core::transport::TransportError,
        );
    }
}
