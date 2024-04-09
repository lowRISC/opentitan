// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use clap::Parser;
use once_cell::sync::Lazy;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
#[allow(dead_code)]
enum TestPhase {
    Init = 0,
    DriveInitial = 1,
    WaitNoWakeup = 2,
    WaitWakeup = 3,
    Done = 4,
}

// Keep this consistent with device code.
const DEBOUNCE_SW_VALUE_USEC: u64 = 100;

static CONFIG: Lazy<Config> = Lazy::new(|| {
    Config {
        // pwrb_in_i, ac_present_i, lid_open_i
        output_pins: vec!["IOR10", "IOR11", "IOR12"],
        open_drain: vec![false, false, false],
        // z3_wakeup
        input_pins: vec!["IOR5"],
        pullup_pins: vec![],
    }
});

const PHASE_PINS: &[&str] = &["IOB0", "IOB1", "IOB2"];

fn setup_phase_pins(transport: &TransportWrapper) -> Result<()> {
    for pin in PHASE_PINS {
        transport.gpio_pin(pin)?.set_mode(PinMode::PushPull)?;
    }
    Ok(())
}

fn set_test_phase(transport: &TransportWrapper, phase: TestPhase) -> Result<()> {
    // Since the transport may not be able to change all pins atomically, we use
    // a Gray code encoding so that it suffices to change one pin to go to
    // the next phase.
    const GRAY_CODE: &[u8] = &[0b000, 0b001, 0b011, 0b010, 0b110];

    let mut val = GRAY_CODE[phase as usize];
    for pin in PHASE_PINS {
        transport.gpio_pin(pin)?.write((val & 1) == 1)?;
        val >>= 1;
    }
    ensure!(val == 0, "test phase value does not fit on the phase pins");
    Ok(())
}

fn sync_with_sw(opts: &Opts, uart: &dyn Uart) -> Result<()> {
    UartConsole::wait_for(uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;
    UartConsole::wait_for(uart, &TestStatus::InTest.wait_pattern(), opts.timeout)?;
    Ok(())
}

fn wait_wakeup_time() {
    std::thread::sleep(Duration::from_micros(DEBOUNCE_SW_VALUE_USEC));
}

fn chip_sw_sysrst_ctrl_ulp_z3_wakeup(
    opts: &Opts,
    transport: &TransportWrapper,
    config: &Config,
    uart: &dyn Uart,
    pins_initial: u8,
    pins_wakeup: u8,
) -> Result<()> {
    // Setup phase pins and set phase to 0 before reset.
    setup_phase_pins(transport)?;
    set_test_phase(transport, TestPhase::Init)?;

    // Reset target.
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    // Set pins to zero.
    set_pins(transport, config, pins_initial)?;

    // Wait until device is ready to accept commands.
    UartConsole::wait_for(uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;

    // Tell device that we have driven pins to the initial value.
    log::info!("Go to PhaseDriveInitial");
    set_test_phase(transport, TestPhase::DriveInitial)?;
    // Wait for device to configure the wakeup source.
    log::info!("Wait for device to configure wakeup source");
    sync_with_sw(opts, uart)?;

    // Wait for the debounce time: the pins are still in the initial value so it should not trigger.
    log::info!("Wait debounce time.");
    wait_wakeup_time();
    // Make sure hardware block has not driven the wakeup pin.
    log::info!("Make sure wakeup pin was not asserted");
    ensure!(read_pins(transport, config)? == 0b0);
    // Tell device that we have done nothing and it should check nothing happened.
    log::info!("Go to PhaseWaitNoWakeup");
    set_test_phase(transport, TestPhase::WaitNoWakeup)?;
    // Wait for device to go to sleep.
    log::info!("Wait for device to sleep");
    UartConsole::wait_for(uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;
    // Set phase for when the device wakes up.
    log::info!("Go to PhaseWaitWakeup");
    set_test_phase(transport, TestPhase::WaitWakeup)?;
    log::info!("Wake up device");
    // We cannot simulate a glitch so simply trigger the wakeup.
    set_pins(transport, config, pins_wakeup)?;
    // Wait for device to wake up.
    log::info!("Wait for device to wake up");
    sync_with_sw(opts, uart)?;
    // Check that the hardware block is correctly driving the wakeup pin and that the
    // EC_RST and FLASH_WP pins are still high.
    log::info!("Make sure wakeup pin was asserted");
    ensure!(read_pins(transport, config)? == 0b1);

    // Finish test.
    log::info!("Go to PhaseDone");
    set_test_phase(transport, TestPhase::Done)?;

    let _ = UartConsole::wait_for(uart, r"PASS!", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    // Setup transport pins.
    setup_pins(&transport, &CONFIG)?;

    // The sysrst_ctrl block can detect three transitions to wakeup:
    // - A high level on the ac_present_i signal
    // - A H -> L transition on the pwrb_in_i signal
    // - A L -> H transition on the lid_open_i signal

    for (initial, wakeup, msg) in [
        (0b000, 0b010, "ac_present_i high"),
        (0b001, 0b000, "pwrb_in_i high to low"),
        (0b000, 0b100, "lid_open_i low to high"),
    ] {
        log::info!("=======================");
        log::info!("Test wakeup using {msg}");
        execute_test!(
            chip_sw_sysrst_ctrl_ulp_z3_wakeup,
            &opts,
            &transport,
            &CONFIG,
            &*uart,
            initial,
            wakeup,
        );
    }
    Ok(())
}
