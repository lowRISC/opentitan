// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use erased_serde::Serialize;

/// `SerializableError` is a trait which represents an error type that can
/// be sent over the wire by the proxy protocol.
#[typetag::serde(tag = "error_type")]
pub trait SerializableError: Serialize + std::error::Error + std::fmt::Debug + Send + Sync {
    fn as_anyhow_error(self: Box<Self>) -> anyhow::Error;
}

/// `impl_serializable_error` needs to be invoked for every error type
/// that can be sent over the wire.
#[macro_export]
macro_rules! impl_serializable_error {
    ($t:ty) => {
        const _: () = {
            use $crate::proxy::errors::SerializableError;
            #[typetag::serde]
            impl SerializableError for $t {
                fn as_anyhow_error(self: Box<$t>) -> anyhow::Error {
                    self.into()
                }
            }
        };
    };
}

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
            crate::bootstrap::BootstrapError,
            crate::bootstrap::LegacyBootstrapError,
            crate::bootstrap::RescueError,
            crate::io::emu::EmuError,
            crate::io::gpio::GpioError,
            crate::io::i2c::I2cError,
            crate::io::spi::SpiError,
            crate::io::uart::UartError,
            crate::transport::TransportError,
            crate::transport::proxy::ProxyError,
        );
    }
}
