// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use erased_serde::Serialize;

#[doc(hidden)]
pub use inventory::submit;

#[doc(hidden)]
pub struct SerializableErrorRegistration {
    pub try_convert: fn(anyhow::Error) -> Result<SerializedError, anyhow::Error>,
}
inventory::collect!(SerializableErrorRegistration);

/// `SerializableError` is a trait which represents an error type that can
/// be sent over the wire.
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
            #[typetag::serde]
            impl $crate::util::serializable_error::SerializableError for $t {
                fn as_anyhow_error(self: Box<$t>) -> anyhow::Error {
                    self.into()
                }
            }

            $crate::util::serializable_error::submit! {
                $crate::util::serializable_error::SerializableErrorRegistration {
                    try_convert: |err| {
                        if !err.is::<$t>() {
                            return Err(err);
                        }

                        let description = err.to_string();
                        let backtrace = format!("{:#?}", err.backtrace());
                        let downcast = err.downcast::<$t>().unwrap();
                        Ok($crate::util::serializable_error::SerializedError {
                            description,
                            backtrace,
                            error: Some(Box::new(downcast)),
                        })
                    }
                }
            };
        };
    };
}

/// `SerializedError` is the wire form of errors that can be sent through network.
#[derive(serde::Serialize, serde::Deserialize, Debug)]
pub struct SerializedError {
    pub description: String,
    pub backtrace: String,
    pub error: Option<Box<dyn SerializableError>>,
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
    fn from(mut error: anyhow::Error) -> SerializedError {
        for reg in inventory::iter::<SerializableErrorRegistration> {
            match (reg.try_convert)(error) {
                Ok(v) => return v,
                Err(e) => error = e,
            }
        }

        let description = error.to_string();
        let backtrace = format!("{:#?}", error.backtrace());
        SerializedError {
            description,
            backtrace,
            error: None,
        }
    }
}
