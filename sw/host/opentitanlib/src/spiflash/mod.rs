// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod flash;
pub mod sfdp;

pub use flash::SpiFlash;
pub use sfdp::{BlockEraseSize, Sfdp, SupportedAddressModes, WriteGranularity};
