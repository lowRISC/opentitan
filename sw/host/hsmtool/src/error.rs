// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::util::attribute::AttributeError;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum HsmError {
    #[error("Token {0:?} not found")]
    TokenNotFound(String),
    #[error("Unknown user {0:?}. Expecting one of {{so, user}}")]
    UnknownUser(String),
    #[error("Key error:  {0}")]
    KeyError(String),
    #[error("Object already exists id={0:?} label={1:?}")]
    ObjectExists(String, String),
    #[error("Bad hash size: expected {0} bytes, but got {1} bytes")]
    HashSizeError(usize, usize),
    #[error("No search criteria. Specify an id or label")]
    NoSearchCriteria,
    #[error("Session required")]
    SessionRequired,
    #[error("Unsupported: {0}")]
    Unsupported(String),
    #[error(transparent)]
    AttributeError(#[from] AttributeError),
    #[error("Object not found for search {0}")]
    ObjectNotFound(String),
    #[error("Expected exactly one object. Found {0} objects for search {1}")]
    TooManyObjects(usize, String),
}
