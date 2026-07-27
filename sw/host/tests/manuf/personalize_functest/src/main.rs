// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use clap::Parser;
use zerocopy::IntoBytes;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::DifLcCtrlState;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc::read_lc_state;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::rpc::ConsoleSend;
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

    /// Path to the scrambling firmware.
    #[arg(long)]
    scrambling_firmware: PathBuf,
}

fn send_rma_unlock_token(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let rma_unlock_token: [u32; 4] = [1, 2, 3, 4];

    // Pre-run scrambling firmware and wait for GPIO signals.
    log::info!(
        "Pre-running scrambling firmware: {:?}",
        opts.scrambling_firmware
    );
    opts.init
        .bootstrap
        .load(transport, &opts.scrambling_firmware)?;

    let error_pin = transport.gpio_pin("IOA0")?;
    error_pin.set_mode(PinMode::Input)?;
    error_pin.set_pull_mode(PullMode::PullDown)?;

    let success_pin = transport.gpio_pin("IOA1")?;
    success_pin.set_mode(PinMode::Input)?;
    success_pin.set_pull_mode(PullMode::PullDown)?;

    let start_pin = transport.gpio_pin("IOA4")?;
    start_pin.set_mode(PinMode::Input)?;
    start_pin.set_pull_mode(PullMode::PullDown)?;

    let t0 = std::time::Instant::now();
    // Wait for Stage 1 to boot and assert TestStart (IOA4) HIGH
    while !start_pin.read()? {
        if t0.elapsed() > opts.timeout {
            return Err(anyhow::anyhow!(
                "Timed out waiting for TestStart (IOA4) from scrambling FW"
            ));
        }
        std::thread::sleep(Duration::from_millis(5));
    }

    // Wait for success_pin (IOA1) or error_pin (IOA0)
    while !success_pin.read()? {
        if error_pin.read()? {
            return Err(anyhow::anyhow!(
                "Scrambling execution failed: TestError pin (IOA0) went HIGH!"
            ));
        }
        if t0.elapsed() > opts.timeout {
            return Err(anyhow::anyhow!(
                "Timed out waiting for Scrambling TestDone (IOA1)"
            ));
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    log::info!("Scrambling completed successfully!");

    // Explicitly release the multiplexed STM32 pins back to SPI alternate mode before we call bootstrap.init()!
    error_pin.set_mode(PinMode::Alternate)?;
    success_pin.set_mode(PinMode::Alternate)?;
    start_pin.set_mode(PinMode::Alternate)?;

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
    let current_lc_state = read_lc_state(transport, &opts.init.jtag_params)?;
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
        /*reset_tap_straps=*/ None,
    )?;
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    // Check the LC state is RMA.
    assert_eq!(
        read_lc_state(transport, &opts.init.jtag_params)?,
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
