// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

mod access;
mod driver;
mod status;

pub use driver::{Driver, I2cDriver, Register, SpiDriver};
