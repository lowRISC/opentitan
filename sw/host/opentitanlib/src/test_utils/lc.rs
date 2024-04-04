// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;

use crate::app::TransportWrapper;
use crate::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use crate::io::jtag::{JtagParams, JtagTap};

pub fn read_lc_state(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    reset_delay: Duration,
) -> Result<DifLcCtrlState> {
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;

    // Apply bootstrap pin to be able to connect to JTAG when ROM execution is
    // enabled.
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
    transport.reset_target(reset_delay, true)?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::LcTap)?;
    let raw_lc_state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;
    transport.pin_strapping("ROM_BOOTSTRAP")?.remove()?;
    DifLcCtrlState::from_redundant_encoding(raw_lc_state)
}
