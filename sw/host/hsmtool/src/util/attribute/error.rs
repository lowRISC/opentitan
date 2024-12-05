// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::AttributeType;
use cryptoki::object::Attribute;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum AttributeError {
    #[error("Invalid data type")]
    InvalidDataType,
    #[error("Encoding error")]
    EncodingError,
    #[error("Unknown attribute: {0:?}")]
    UnknownAttribute(Attribute),
    #[error("Unknown attribute type: {0:?}")]
    UnknownAttributeType(AttributeType),
    #[error("Attribute not found: {0:?}")]
    AttributeNotFound(AttributeType),
}
