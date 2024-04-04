// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
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

use sysrst_ctrl::{read_pins, set_pins, setup_pins, Config};

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

struct Params<'a> {
    opts: &'a Opts,
    transport: &'a TransportWrapper,
    uart: &'a dyn Uart,
    config: &'a Config,
    test_phase_addr: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum TestPhase {
    // There is a Setup phase but this is the initial value on the device code so we do not need it.
    Loopback = 1,
    OverrideSetup = 2,
    OverrideZeros = 3,
    OverrideOnes = 4,
    OverrideRelease = 5,
    OverrideAndLoopback = 6,
    Done = 7,
}

static CONFIG: Lazy<Config> = Lazy::new(|| {
    Config {
        // key0_in, key1_in, key2_in, pwrb_in
        output_pins: vec!["IOR10", "IOR11", "IOR12", "IOR5"],
        open_drain: vec![false, false, false, false],
        // key0_out, key1_out, key2_out, pwrb_out, bat_dis_out, z3_wakeup_out, ec_rst, flash_wp
        input_pins: vec![
            "IOR6",
            "IOR7",
            "IOB0",
            "IOB1",
            "IOB2",
            "IOB3",
            "SYSRST_CTRL_EC_RST_L",
            "SYSRST_CTRL_FLASH_WP_L",
        ],
        // ec_rst, flash_wp
        pullup_pins: vec!["SYSRST_CTRL_EC_RST_L", "SYSRST_CTRL_FLASH_WP_L"],
    }
});

const OUTPUT_ALL_SET: u8 = 0b11111111;
const OUTPUT_NONE_SET: u8 = 0b00000000;
const LOOPBACK_ALL_SET: u8 = 0b1111;
const LOOPBACK_PARTIAL_SET: u8 = 0b1010;
const LOOPBACK_PATTERN_LENGTH: usize = 16;

fn set_loopback_pads(params: &Params, pad_values: u8) -> Result<()> {
    set_pins(params.transport, params.config, pad_values)
}

fn read_loopback_pads(params: &Params) -> Result<u8> {
    // Only capture the pins of interest.
    Ok(read_pins(params.transport, params.config)? & LOOPBACK_ALL_SET)
}

fn read_output_pads(params: &Params) -> Result<u8> {
    read_pins(params.transport, params.config)
}

fn check_loopback_single(params: &Params) -> Result<()> {
    set_loopback_pads(params, LOOPBACK_PARTIAL_SET)?;
    ensure!(read_loopback_pads(params)? == LOOPBACK_PARTIAL_SET);
    Ok(())
}

fn check_loopback_pattern(params: &Params) -> Result<()> {
    for i in 0..LOOPBACK_PATTERN_LENGTH {
        let pattern = i as u8;
        set_loopback_pads(params, pattern)?;
        ensure!(read_loopback_pads(params)? == pattern);
    }
    Ok(())
}

fn sync_with_sw(params: &Params) -> Result<()> {
    UartConsole::wait_for(
        params.uart,
        &TestStatus::InWfi.wait_pattern(),
        params.opts.timeout,
    )?;
    Ok(())
}

fn chip_sw_sysrst_ctrl_input(params: &Params) -> Result<()> {
    // Setup transport pins.
    setup_pins(params.transport, params.config)?;

    // Wait until device has setup pins.
    sync_with_sw(params)?;

    // Ask device to wait while we test loopback.
    MemWriteReq::execute(
        params.uart,
        params.test_phase_addr,
        &[TestPhase::Loopback as u8],
    )?;
    sync_with_sw(params)?;
    check_loopback_pattern(params)?;

    // Ask device to setup overrides.
    MemWriteReq::execute(
        params.uart,
        params.test_phase_addr,
        &[TestPhase::OverrideSetup as u8],
    )?;
    sync_with_sw(params)?;

    // Ask device to override all pins to zero.
    MemWriteReq::execute(
        params.uart,
        params.test_phase_addr,
        &[TestPhase::OverrideZeros as u8],
    )?;
    sync_with_sw(params)?;
    // Set all pins to one.
    set_loopback_pads(params, LOOPBACK_ALL_SET)?;
    // Make sure loopback reads all zeros.
    ensure!(read_output_pads(params)? == OUTPUT_NONE_SET);

    // Ask device to override all pins to one.
    MemWriteReq::execute(
        params.uart,
        params.test_phase_addr,
        &[TestPhase::OverrideOnes as u8],
    )?;
    sync_with_sw(params)?;
    // Set all pins to zero.
    set_loopback_pads(params, 0)?;
    // Make sure loopback reads all ones.
    ensure!(read_output_pads(params)? == OUTPUT_ALL_SET);

    // Ask device to release overrides.
    MemWriteReq::execute(
        params.uart,
        params.test_phase_addr,
        &[TestPhase::OverrideRelease as u8],
    )?;
    sync_with_sw(params)?;
    // Check loopback is now working again.
    check_loopback_single(params)?;

    // Ask device to override some pins.
    MemWriteReq::execute(
        params.uart,
        params.test_phase_addr,
        &[TestPhase::OverrideAndLoopback as u8],
    )?;
    sync_with_sw(params)?;
    // Check loopback is partially working.
    ensure!(read_loopback_pads(params)? == LOOPBACK_ALL_SET);

    // Ask device to finish test.
    MemWriteReq::execute(
        params.uart,
        params.test_phase_addr,
        &[TestPhase::Done as u8],
    )?;

    let _ = UartConsole::wait_for(params.uart, r"PASS!", params.opts.timeout)?;
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
        .find(|symbol| symbol.name() == Ok("kTestPhaseReal"))
        .expect("Provided ELF missing 'kTestPhaseReal' symbol");
    assert_eq!(
        symbol.size(),
        1,
        "symbol 'kTestPhaseReal' does not have the expected size"
    );

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(
        chip_sw_sysrst_ctrl_input,
        &Params {
            opts: &opts,
            transport: &transport,
            uart: &*uart,
            config: &CONFIG,
            test_phase_addr: symbol.address() as u32,
        }
    );
    Ok(())
}
