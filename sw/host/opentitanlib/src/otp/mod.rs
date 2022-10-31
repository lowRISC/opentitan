// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod alert_handler;
pub mod alert_handler_regs;
pub mod lc_state;
// TODO(lowRISC/opentitan#15443): Fix this lint.
#[allow(clippy::module_inception)]
pub mod otp_img;
