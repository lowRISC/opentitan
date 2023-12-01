// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stabilised in Rust 1.74, can be removed when we upgrade.
#![feature(io_error_other)]
// Used for serde_annotate.
#![feature(min_specialization)]

pub mod app;
pub mod backend;
pub mod bootstrap;
pub mod chip;
pub mod console;
pub mod crypto;
pub mod dif;
pub mod image;
pub mod io;
pub mod otp;
pub mod proxy;
pub mod spiflash;
pub mod test_utils;
pub mod tpm;
pub mod transport;
pub mod uart;
pub mod util;
