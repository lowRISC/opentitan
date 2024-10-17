// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;
use std::time::Duration;

use anyhow::Result;
use clap::Parser;
use zerocopy::AsBytes;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::DifLcCtrlState;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc::read_lc_state;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::rpc::UartSend;
use opentitanlib::uart::console::UartConsole;
use util_lib::hash_lc_token;

mod provisioning_data;
use provisioning_data::LcTokenHash;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn send_rma_unlock_token(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let rma_unlock_token: [u32; 4] = [1, 2, 3, 4];
    // Wait for the program to complete SECRET1 configuration and apply a ROM
    // bootstrap operation. This is needed because the flash scrambling key
    // may cause the flash contents to be garbled after locking the SECRET1
    // partition.
    let _ = UartConsole::wait_for(&*uart, r"Provisioning OTP SECRET1 Done ...", opts.timeout)?;
    uart.clear_rx_buffer()?;
    opts.init.bootstrap.init(transport)?;

    let _ = UartConsole::wait_for(
        &*uart,
        r"Waiting For RMA Unlock Token Hash ...",
        opts.timeout,
    )?;

    let rma_token_hash = LcTokenHash {
        hash: hash_lc_token(rma_unlock_token.as_bytes())?,
    };

    rma_token_hash.send_with_crc(&*uart)?;

    let _ = UartConsole::wait_for(
        &*uart,
        r"Finished provisioning OTP SECRET2 and keymgr flash info pages ...",
        opts.timeout,
    )?;
    // Check the LC state is Dev or Prod.
    let current_lc_state = read_lc_state(
        transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
    )?;
    let valid_lc_states = HashSet::from([DifLcCtrlState::Dev, DifLcCtrlState::Prod]);
    assert!(
        valid_lc_states.contains(&current_lc_state),
        "Invalid initial LC state (must be in Dev or Prod to test transition to RMA).",
    );

    // Attempt to transition to RMA to check the validity of the RMA unlock token.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
    let jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)?;
    trigger_lc_transition(
        transport,
        jtag,
        DifLcCtrlState::Rma,
        Some(rma_unlock_token),
        /*use_external_clk=*/ false,
        opts.init.bootstrap.options.reset_delay,
        /*reset_tap_straps=*/ None,
    )?;
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    // Check the LC state is RMA.
    assert_eq!(
        read_lc_state(
            transport,
            &opts.init.jtag_params,
            opts.init.bootstrap.options.reset_delay,
        )?,
        DifLcCtrlState::Rma,
        "Did not transition to RMA.",
    );

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(send_rma_unlock_token, &opts, &transport);

    Ok(())
}
