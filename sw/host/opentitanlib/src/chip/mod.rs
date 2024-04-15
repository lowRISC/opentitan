// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use thiserror::Error;

pub mod alert;
pub mod autogen;
pub mod boolean;
pub mod boot_log;
pub mod boot_svc;
pub mod helper;

#[derive(Debug, Error)]
pub enum ChipDataError {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Anyhow(#[from] anyhow::Error),
    #[error("bad size: expected {0} bytes, but found {1}")]
    BadSize(usize, usize),
    #[error("invalid digest")]
    InvalidDigest,
}
