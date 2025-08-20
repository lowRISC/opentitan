// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use clap::Parser;
use std::time::Duration;

use opentitanlib::app::{TransportWrapper, UartRx};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::util::parse_int::ParseInt;
use ot_hal::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Duration of the reset pulse.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "60s")]
    pub timeout: Duration,

    /// Wait for regex from the console before reading status from JTAG.
    #[arg(long)]
    wait_for: String,

    #[arg(long, value_parser = u32::from_str)]
    rom_ext_version: u32,
    #[arg(long, value_parser = u32::from_str)]
    rom_ext_sec_version: u32,
    #[arg(long, value_parser = u32::from_str)]
    owner_fw_version: u32,
    #[arg(long, value_parser = u32::from_str)]
    device_status: u32,
}

fn check_device_status(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Reset the chip, select the LC TAP, and connect to it.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset(UartRx::Clear)?;
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)?;

    let uart = transport.uart("console").context("failed to get UART")?;
    let _ = UartConsole::wait_for(&*uart, &opts.wait_for, opts.timeout)?;

    let lc_state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    let hw0 = jtag.read_lc_ctrl_reg(&LcCtrlReg::HwRevision0)?;
    let hw1 = jtag.read_lc_ctrl_reg(&LcCtrlReg::HwRevision1)?;
    log::info!(
        "Hardware device {hw0:08x}:{hw1:02x} in lc_state {}({lc_state:08x})",
        DifLcCtrlState::from_redundant_encoding(lc_state)?.lc_state_to_str()
    );

    lc_transition::claim_lc_mutex(&mut *jtag, true)?;
    let rom_ext_version = jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionToken0)?;
    let rom_ext_sec_version = jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionToken1)?;
    let owner_fw_version = jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionToken2)?;
    let device_status = jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionToken3)?;
    lc_transition::claim_lc_mutex(&mut *jtag, false)?;

    log::info!("rom_ext_version:     {rom_ext_version}");
    log::info!("rom_ext_sec_version: {rom_ext_sec_version}");
    log::info!("owner_fw_version:    {owner_fw_version}");
    log::info!("device_status:       {device_status}");

    assert_eq!(
        opts.rom_ext_version, rom_ext_version,
        "testing rom_ext_version"
    );
    assert_eq!(
        opts.rom_ext_sec_version, rom_ext_sec_version,
        "testing rom_ext_sec_version"
    );
    assert_eq!(
        opts.owner_fw_version, owner_fw_version,
        "testing owner_fw_version"
    );
    assert_eq!(opts.device_status, device_status, "testing device_status");

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(check_device_status, &opts, &transport);

    Ok(())
}
