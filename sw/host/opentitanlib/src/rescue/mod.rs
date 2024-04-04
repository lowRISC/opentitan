// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use thiserror::Error;

pub mod serial;
pub mod xmodem;

#[derive(Debug, Error)]
pub enum RescueError {
    #[error("bad mode: {0}")]
    BadMode(String),
}
