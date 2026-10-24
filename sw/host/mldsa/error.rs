// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use thiserror::Error;

#[derive(Debug, Error)]
pub enum MldsaError {
    #[error("Unexpected key length {0}")]
    BadKeyLength(usize),

    #[error("parse error: {0}")]
    ParseError(String),

    #[error("failed to obtain randomness: {0}")]
    Rng(#[from] ml_dsa::common::getrandom::Error),

    #[error(transparent)]
    Der(#[from] pkcs8::der::Error),

    #[error(transparent)]
    Pkcs8(#[from] pkcs8::Error),

    #[error(transparent)]
    Io(#[from] std::io::Error),

    #[error(transparent)]
    Pem(#[from] pkcs8::der::pem::Error),
}
