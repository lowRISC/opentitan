// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use thiserror::Error;

pub mod boot_log;
pub mod boot_svc;
pub mod serial;
pub mod xmodem;

#[derive(Debug, Error)]
pub enum RescueError {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error("bad mode: {0}")]
    BadMode(String),
    #[error("bad size: expected {0} bytes, but found {1}")]
    BadSize(usize, usize),
    #[error("invalid digest")]
    InvalidDigest,
}
