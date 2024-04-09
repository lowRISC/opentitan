// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod aon_timer;
// The "english breakfast" variant of the chip doesn't have the same
// set of CSRs as the "earlgrey" chip.
#[cfg(not(feature = "english_breakfast"))]
pub mod clkmgr;
pub mod lc_ctrl;
pub mod otp_ctrl;
pub mod rstmgr;
pub mod uart;
