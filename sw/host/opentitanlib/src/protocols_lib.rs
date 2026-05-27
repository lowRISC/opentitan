// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Transfer, boot, signing and test protocols for OpenTitan host-side logic.

pub mod bootstrap;
pub mod console;
pub mod otp;
pub mod proxy;
pub mod rescue;
pub mod spiflash;
pub mod tpm;
