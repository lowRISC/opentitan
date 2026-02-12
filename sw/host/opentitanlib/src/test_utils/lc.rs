// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use arrayvec::ArrayVec;

use ot_hal::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg, LcCtrlStatus};

use crate::app::{TransportWrapper, UartRx};
use crate::io::jtag::{JtagParams, JtagTap};
use crate::test_utils::lc_transition::wait_for_status;

pub fn read_lc_state(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
) -> Result<DifLcCtrlState> {
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;

    // Apply bootstrap pin to be able to connect to JTAG when ROM execution is
    // enabled.
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
    transport.reset(UartRx::Clear)?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::LcTap)?;
    // We must wait for the lc_ctrl to initialize before the LC state is exposed.
    wait_for_status(
        &mut *jtag,
        Duration::from_secs(1),
        LcCtrlStatus::INITIALIZED,
    )?;
    let raw_lc_state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;
    transport.pin_strapping("ROM_BOOTSTRAP")?.remove()?;
    DifLcCtrlState::from_redundant_encoding(raw_lc_state)
}

pub fn read_device_id(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
) -> Result<ArrayVec<u32, 8>> {
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;

    // Apply bootstrap pin to be able to connect to JTAG when ROM execution is
    // enabled.
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
    transport.reset(UartRx::Clear)?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::LcTap)?;
    // We must wait for the lc_ctrl to initialize before the LC state is exposed.
    wait_for_status(
        &mut *jtag,
        Duration::from_secs(1),
        LcCtrlStatus::INITIALIZED,
    )?;

    let mut device_id = ArrayVec::<u32, 8>::new();
    device_id.push(jtag.read_lc_ctrl_reg(&LcCtrlReg::DeviceId0)?);
    device_id.push(jtag.read_lc_ctrl_reg(&LcCtrlReg::DeviceId1)?);
    device_id.push(jtag.read_lc_ctrl_reg(&LcCtrlReg::DeviceId2)?);
    device_id.push(jtag.read_lc_ctrl_reg(&LcCtrlReg::DeviceId3)?);
    device_id.push(jtag.read_lc_ctrl_reg(&LcCtrlReg::DeviceId4)?);
    device_id.push(jtag.read_lc_ctrl_reg(&LcCtrlReg::DeviceId5)?);
    device_id.push(jtag.read_lc_ctrl_reg(&LcCtrlReg::DeviceId6)?);
    device_id.push(jtag.read_lc_ctrl_reg(&LcCtrlReg::DeviceId7)?);

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;
    transport.pin_strapping("ROM_BOOTSTRAP")?.remove()?;

    Ok(device_id)
}
