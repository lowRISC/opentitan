// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use object::{Object, ObjectSymbol};
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::MemWriteReq;
use opentitanlib::test_utils::test_status::TestStatus;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::{collection, execute_test};

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

struct Config {
    // List to the IO names of the transport, the order should match the pin
    // values in `kTestExpected` on the device C code: the ith item corresponds
    // to the i-th bit.
    pins: Vec<&'static str>,
    // If true, the pin will be setup in open drain mode (with a pullup), otherwise
    // in push-pull mode. The order must match the one in pins.
    open_drain: Vec<bool>,
}

static CONFIG: Lazy<HashMap<&'static str, Config>> = Lazy::new(|| {
    collection! {
        "hyper310" => Config {
            pins: vec!["IOR10", "IOR11", "IOR12", "IOR5", "IOR6", "IOR7", "IOR8", "IOR9"],
            open_drain: vec![false, false, false, false, false, false, true, true],
        },
    }
});

/// Configure earlgrey and debugger pins.
fn setup_pins(transport: &TransportWrapper, config: &Config) -> Result<()> {
    log::info!("Configuring transport GPIOs");
    // Since the EC reset and flash WP pins are open drain, configure those hyperdebug pins as
    // open drain with pullup.
    assert_eq!(config.pins.len(), config.open_drain.len());
    for (pin,od) in std::iter::zip(&config.pins, &config.open_drain) {
        log::info!("pin {}: {}", pin, od);
        if *od {
            transport.gpio_pin(pin)?.set_mode(PinMode::OpenDrain)?;
            transport.gpio_pin(pin)?.set_pull_mode(PullMode::PullUp)?;
        }
        else {
            transport.gpio_pin(pin)?.set_mode(PinMode::PushPull)?;
        }
    }
    Ok(())
}

fn set_pins(transport: &TransportWrapper, config: &Config, values: u8) -> Result<()> {
    log::info!("Set pins to {:b}", values);
    // Set pins on the transport.
    for (i, pin) in config.pins.iter().enumerate() {
        transport
            .gpio_pin(pin)?
            .write(((values >> i) & 0b1) == 0b1)?;
    }
    Ok(())
}

fn chip_sw_sysrst_ctrl_input(
    opts: &Opts,
    transport: &TransportWrapper,
    config: &Config,
    test_phase_addr: u32,
    test_expected_addr: u32,
) -> Result<()> {
    let uart = transport.uart("console")?;

    /* Setup transport pins */
    setup_pins(transport, config)?;

    /* Follow the sequence as in
     * hw/top_earlgrey/dv/env/seq_lib/chip_sw_sysrst_ctrl_inputs_vseq.sv */
    let phase_values = [
        0b00000000u8, /* Phase 0 */
        0b00000001u8,
        0b00000010u8,
        0b00000100u8,
        0b00001000u8,
        0b00010000u8,
        0b00100000u8,
        0b01000000u8,
        0b10000000u8,
        0b11111111u8, /* Phase 9 */
    ];

    for (phase_idx, pin_values) in phase_values.into_iter().enumerate() {
        /* Set the pins to the right values */
        set_pins(transport, config, pin_values)?;
        /* Set kTestExpected on the device */
        log::info!(
            "Set expected value to {:x} and phase to {}",
            pin_values,
            phase_idx
        );
        MemWriteReq::execute(&*uart, test_expected_addr, &[pin_values])?;
        /* Set kTestPhase on the device */
        MemWriteReq::execute(&*uart, test_phase_addr, &[phase_idx as u8])?;
        /* Wait until the device does test_set_status(kStatusWfi) */
        UartConsole::wait_for(&*uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;
    }
    let _ = UartConsole::wait_for(&*uart, r"PASS!", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    /* Load the ELF binary and get the address of the `kPhase` variable
     * in example_sival.c */
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let elf_file = object::File::parse(&*elf_binary)?;
    let mut symbols = HashMap::<String, (u32, u64)>::new();
    for sym in elf_file.symbols() {
        symbols.insert(sym.name()?.to_owned(), (sym.address() as u32, sym.size()));
    }
    let (test_phase_address, test_phase_size) = symbols
        .get("kTestPhaseReal")
        .expect("Provided ELF missing 'kTestPhaseReal' symbol");
    assert_eq!(
        *test_phase_size, 1,
        "symbol 'kTestPhaseReal' does not have the expected size"
    );
    let (test_expected_address, test_expected_size) = symbols
        .get("kTestExpectedReal")
        .expect("Provided ELF missing 'kTestExpectedReal' symbol");
    assert_eq!(
        *test_expected_size, 1,
        "symbol 'kTestExpectedReal' does not have the expected size"
    );

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    log::info!(
        "Use pin configuration for {:?}",
        opts.init.backend_opts.interface
    );
    let config = CONFIG
        .get(opts.init.backend_opts.interface.as_str())
        .expect("interface");

    execute_test!(
        chip_sw_sysrst_ctrl_input,
        &opts,
        &transport,
        config,
        *test_phase_address,
        *test_expected_address
    );
    Ok(())
}
