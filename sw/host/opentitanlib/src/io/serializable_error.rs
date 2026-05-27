// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Serialization trait for errors.

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
            use $crate::io::serializable_error::SerializableError;
            #[typetag::serde]
            impl SerializableError for $t {
                fn as_anyhow_error(self: Box<$t>) -> anyhow::Error {
                    self.into()
                }
            }
        };
    };
}
