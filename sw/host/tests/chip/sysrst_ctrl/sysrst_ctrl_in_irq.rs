// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use once_cell::sync::Lazy;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use object::{Object, ObjectSymbol};
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::MemWriteReq;
use opentitanlib::test_utils::test_status::TestStatus;
use opentitanlib::uart::console::UartConsole;

use sysrst_ctrl::{set_pins, setup_pins, Config};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

static CONFIG: Lazy<Config> = Lazy::new(|| {
    Config {
        /* The order of those pins must match the order in the DV's set_pad
         * function, that is:  power button, key0, key1, key2, AC, EC, WP. */
        output_pins: vec![
            "IOR5",
            "IOR10",
            "IOR11",
            "IOR12",
            "IOR6",
            "SYSRST_CTRL_EC_RST_L",
            "SYSRST_CTRL_FLASH_WP_L",
        ],
        open_drain: vec![false, false, false, false, false, true, true],
        input_pins: vec![],
        //  ec_rst, flash_wp
        pullup_pins: vec!["SYSRST_CTRL_EC_RST_L", "SYSRST_CTRL_FLASH_WP_L"],
    }
});

fn sync_with_sw(opts: &Opts, uart: &dyn Uart) -> Result<()> {
    UartConsole::wait_for(uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;
    Ok(())
}

struct TestParams<'a> {
    opts: &'a Opts,
    transport: &'a TransportWrapper,
    uart: &'a dyn Uart,
    config: &'a Config,
    test_phase_addr: u32,
}

fn set_pads_and_synch(
    params: &TestParams,
    pad_values_prev: u8,
    pad_values_next: u8,
    test_phase: &mut u8,
) -> Result<()> {
    // The tests expects first a glitch that should not trigger the interrupt.
    // Since we cannot generate a short enough glitch, simply do not change the pins
    // and check that no interrupt is generated.
    log::info!("==============================");
    log::info!(
        "Test with prev={:x}, next={:x}",
        pad_values_prev,
        pad_values_next
    );

    // Set pins.
    set_pins(params.transport, params.config, pad_values_prev)?;
    // Advance phase to let device side setup the interrupt.
    log::info!("Tell device to setup");
    MemWriteReq::execute(params.uart, params.test_phase_addr, &[*test_phase])?;
    *test_phase += 1;
    // Wait for device to notify that setup is done.
    log::info!("Wait for device to finish setup");
    sync_with_sw(params.opts, params.uart)?;
    // Here, do NOT generate a glitch.
    // Advance phase to let device that we have "generated" the glitch.
    log::info!("Tell device to wait for glitch");
    MemWriteReq::execute(params.uart, params.test_phase_addr, &[*test_phase])?;
    *test_phase += 1;
    // Wait for device to check that no interrupt was generated.
    log::info!("Wait device to acknowledge undetected glitch");
    sync_with_sw(params.opts, params.uart)?;
    // Change the input.
    set_pins(params.transport, params.config, pad_values_next)?;
    // Wait for device to acknowledge the interrupt.
    log::info!("Wait device to acknowledge to interrupt");
    sync_with_sw(params.opts, params.uart)?;

    Ok(())
}

fn chip_sw_sysrst_ctrl_in_irq(
    opts: &Opts,
    transport: &TransportWrapper,
    uart: &dyn Uart,
    config: &Config,
    test_phase_addr: u32,
) -> Result<()> {
    /* Setup transport pins */
    setup_pins(transport, config)?;

    let params = TestParams {
        opts,
        transport,
        uart,
        config,
        test_phase_addr,
    };

    // Test 7 H2L input transitions.
    let mut test_phase = 0;
    for i in 0..7 {
        set_pads_and_synch(&params, 1 << i, 0, &mut test_phase)?;
    }
    // Test 7 L2H input transitions.
    for i in 0..7 {
        set_pads_and_synch(&params, 0, 1 << i, &mut test_phase)?;
    }

    // Test 4 different combo key intr sources with 2, 3, 4 and 5 combo key
    // transition H2L.
    set_pads_and_synch(&params, 0b00000011, 0b00000000, &mut test_phase)?;

    set_pads_and_synch(&params, 0b00011100, 0b00000000, &mut test_phase)?;

    set_pads_and_synch(&params, 0b00011011, 0b00000000, &mut test_phase)?;

    set_pads_and_synch(&params, 0b00011111, 0b00000000, &mut test_phase)?;

    let _ = UartConsole::wait_for(uart, r"PASS!", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let elf_binary = fs::read(&opts.firmware_elf)?;
    let elf_file = object::File::parse(&*elf_binary)?;
    let symbol = elf_file
        .symbols()
        .find(|symbol| symbol.name() == Ok("kCurrentTestPhaseReal"))
        .expect("Provided ELF missing 'kCurrentTestPhaseReal' symbol");
    assert_eq!(
        symbol.size(),
        1,
        "symbol 'kCurrentTestPhaseReal' does not have the expected size"
    );

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(
        chip_sw_sysrst_ctrl_in_irq,
        &opts,
        &transport,
        &*uart,
        &CONFIG,
        symbol.address() as u32,
    );
    Ok(())
}
