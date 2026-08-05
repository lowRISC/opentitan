// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use thiserror::Error;

#[derive(Debug, Error)]
pub enum SlhDsaError {
    #[error("Unrecognised OID")]
    BadOid,

    #[error("Unexpected signature length {0}")]
    BadSigLength(usize),

    #[error("Unexpected key length {0}")]
    BadKeyLength(usize),

    #[error("parse error: {0}")]
    ParseError(String),

    #[error(transparent)]
    Io(#[from] std::io::Error),

    #[error(transparent)]
    Pem(#[from] pem_rfc7468::Error),
}
