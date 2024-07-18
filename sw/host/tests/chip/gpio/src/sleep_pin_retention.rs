// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use clap::Parser;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

const GPIO_PINS: &[&str] = &["IOB0", "IOB1", "IOB2", "IOB3"];
const NUM_GPIO_PINS: usize = GPIO_PINS.len();
const WAKEUP_PIN: &str = "IOR10";
const SYNC_PIN: &str = "IOR11";

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn read_pins(transport: &TransportWrapper, pins: &[&str]) -> Result<u8> {
    ensure!(pins.len() <= 8);
    let mut values = 0u8;
    for (i, pin) in pins.iter().enumerate() {
        if transport.gpio_pin(pin)?.read()? {
            values |= 1 << i;
        }
    }
    Ok(values)
}

fn sleep_pin_retention_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    log::info!("Starting host side");

    transport
        .gpio_pin(WAKEUP_PIN)?
        .set_mode(PinMode::PushPull)?;
    transport.gpio_pin(SYNC_PIN)?.set_mode(PinMode::PushPull)?;
    for pin in GPIO_PINS {
        transport.gpio_pin(pin)?.set_mode(PinMode::Input)?;
    }

    let vec = UartConsole::wait_for(&*uart, r"Num Rounds: +([0-9]+)\r\n", opts.timeout)?;
    let num_rounds: i32 = vec[1].parse()?;
    log::info!("Doing {:?} rounds of testing", num_rounds);

    for _ in 0..num_rounds {
        transport.gpio_pin(WAKEUP_PIN)?.write(false)?; // Don't wake up on the positive edge yet.
        transport.gpio_pin(SYNC_PIN)?.write(false)?; // Not done with this round yet.

        let vec =
            UartConsole::wait_for(&*uart, r"Chosen GPIO value: +([0-9a-fA-F]+)", opts.timeout)?;
        let gpio_awake_value = u8::from_str_radix(&vec[1], 16)?;
        log::info!("Chosen GPIO value 0x{:x}", gpio_awake_value);
        let gpio_sleep_value = !gpio_awake_value & ((1 << NUM_GPIO_PINS) - 1);

        UartConsole::wait_for(&*uart, r"Entering low power mode.", opts.timeout)?;
        log::info!("Detected device entering low power mode");

        let pin_values = read_pins(transport, GPIO_PINS)?;
        log::info!("Read GPIO value 0x{:x}", pin_values);
        ensure!(
            pin_values == gpio_sleep_value,
            "GPIO pin value 0x{:x} does not match the expected sleep value 0x{:x}",
            pin_values,
            gpio_sleep_value
        );

        transport.gpio_pin(WAKEUP_PIN)?.write(true)?; // Wake up on the positive edge.
        log::info!("Triggered wake up");

        UartConsole::wait_for(&*uart, r"Woke up from low power mode.", opts.timeout)?;
        log::info!("Detected wake up");

        let pin_values = read_pins(transport, GPIO_PINS)?;
        log::info!(
            "Read GPIO value 0x{:x} expected 0x{:x}",
            pin_values,
            gpio_awake_value
        );
        ensure!(
            pin_values == gpio_awake_value,
            "GPIO pin value 0x{:x} does not match the expected awake value 0x{:x}",
            pin_values,
            gpio_awake_value
        );

        transport.gpio_pin(SYNC_PIN)?.write(true)?; // Signal OK to finish this round now.
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(sleep_pin_retention_test, &opts, &transport);
    Ok(())
}
