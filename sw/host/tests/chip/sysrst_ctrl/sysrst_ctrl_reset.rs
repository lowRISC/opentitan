// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use clap::Parser;
use once_cell::sync::Lazy;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
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
        // key0, key1, key2, pwrb_in, ac_present_in, lid_open
        output_pins: vec!["IOR10", "IOR11", "IOR12", "IOR5", "IOR6", "IOR7"],
        open_drain: vec![false, false, false, false, false, false],
        input_pins: vec!["SYSRST_CTRL_EC_RST_L", "SYSRST_CTRL_FLASH_WP_L"],
        //  ec_rst, flash_wp
        pullup_pins: vec!["SYSRST_CTRL_EC_RST_L", "SYSRST_CTRL_FLASH_WP_L"],
    }
});

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
#[allow(dead_code)]
enum TestPhase {
    CheckComboReset = 0,
    CheckDeepSleepWakeup = 1,
    CheckDeepSleepReset = 2,
    FinalCheck = 3,
}

const PHASE_PINS: &[&str] = &["IOB0", "IOB1"];

// Before CheckComboReset: all pins high.
const PADS_VALUE_INIT: u8 = 0b111111;
// Trigger reset in CheckComboReset: key0 and key1 low.
// Also prepare for next phase: ac present low, power button high, lid open low.
const PADS_VALUE_COMBO_RESET: u8 = 0b001100;
// Trigger wakeup in CheckDeepSleepWakeup: lid open high.
const PADS_VALUE_WAKEUP: u8 = 0b101100;
// Trigger sleep reset in CheckDeepSleepReset: key2 and power button low.
const PADS_VALUE_SLEEP_RESET: u8 = 0b100000;
// Combo action detection time: set to around 5ms on the device.
const COMBO_DETECTION_TIME: Duration = Duration::from_micros(10_000);

fn setup_phase_pins(transport: &TransportWrapper) -> Result<()> {
    for pin in PHASE_PINS {
        transport.gpio_pin(pin)?.set_mode(PinMode::PushPull)?;
    }
    Ok(())
}

fn set_test_phase(transport: &TransportWrapper, phase: TestPhase) -> Result<()> {
    let mut val = phase as u8;
    for pin in PHASE_PINS {
        transport.gpio_pin(pin)?.write((val & 1) == 1)?;
        val >>= 1;
    }
    ensure!(val == 0, "test phase value does not fit on the phase pins");
    Ok(())
}

fn chip_sw_sysrst_ctrl_reset(
    opts: &Opts,
    transport: &TransportWrapper,
    uart: &dyn Uart,
    config: &Config,
) -> Result<()> {
    // Setup transport pins.
    setup_pins(transport, config)?;
    setup_phase_pins(transport)?;

    let flash_wp_pin = transport.gpio_pin("SYSRST_CTRL_FLASH_WP_L")?;
    let ec_rst_pin = transport.gpio_pin("SYSRST_CTRL_EC_RST_L")?;

    // Set first phase and pins in a good state.
    set_test_phase(transport, TestPhase::CheckComboReset)?;
    set_pins(transport, config, PADS_VALUE_INIT)?;
    // Reset target.
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Wait until target has prepared for the test.
    UartConsole::wait_for(uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;
    // Verify that the device has release EC reset and flash WP pins.
    ensure!(
        flash_wp_pin.read()?,
        "flash_wp_l does not have the expected value"
    );
    ensure!(
        ec_rst_pin.read()?,
        "ec_rst_l does not have the expected value"
    );
    // Set test phase pins for after reset.
    set_test_phase(transport, TestPhase::CheckDeepSleepWakeup)?;
    // Trigger combo reset.
    set_pins(transport, config, PADS_VALUE_COMBO_RESET)?;
    // Wait for combo detection.
    std::thread::sleep(COMBO_DETECTION_TIME);
    // Verify that the flash WP was pulled down.
    ensure!(
        !flash_wp_pin.read()?,
        "flash_wp_l does not have the expected value"
    );
    // The EC reset pin must have been pulled down and then released so don't check.

    // Wait until target has prepared for the test.
    UartConsole::wait_for(uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;
    // Set test phase pins for after wakeup.
    set_test_phase(transport, TestPhase::CheckDeepSleepReset)?;
    // Trigger wakeup.
    set_pins(transport, config, PADS_VALUE_WAKEUP)?;

    // Wait until target has prepared for the test.
    UartConsole::wait_for(uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;
    // Make sure device has released flash wp.
    ensure!(
        flash_wp_pin.read()?,
        "flash_wp_l does not have the expected value"
    );
    // Set test phase pins for after reset.
    set_test_phase(transport, TestPhase::FinalCheck)?;
    // Trigger combo reset.
    set_pins(transport, config, PADS_VALUE_SLEEP_RESET)?;
    // Wait for combo detection.
    std::thread::sleep(COMBO_DETECTION_TIME);
    // Verify that EC reset and flash WP pins are immediately pulled down.
    ensure!(
        !flash_wp_pin.read()?,
        "flash_wp_l does not have the expected value"
    );
    // The EC reset pin must have been pulled down and then released so don't check.

    let _ = UartConsole::wait_for(uart, r"PASS!", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(
        chip_sw_sysrst_ctrl_reset,
        &opts,
        &transport,
        &*uart,
        &CONFIG
    );
    Ok(())
}
