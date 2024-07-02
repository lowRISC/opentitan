// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::Parser;
use regex::Regex;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::{GpioPin, PinMode, PullMode};
use opentitanlib::io::spi::Transfer;
use opentitanlib::io::uart::Uart;
use opentitanlib::spiflash::SpiFlash;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "BOOTSTRAP")]
    spi: String,
}

const SLEEP: bool = true;
const AWAKE: bool = false;

fn spi_sleep_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    let sleep_pin = transport.gpio_pin("IOA8")?;
    sleep_pin.set_mode(PinMode::PushPull)?;
    let sleep_indicator = transport.gpio_pin("IOA7")?;
    sleep_indicator.set_mode(PinMode::Input)?;
    sleep_indicator.set_pull_mode(PullMode::PullUp)?;

    sleep_pin.write(AWAKE)?;
    transport.pin_strapping("RESET")?.remove()?;
    while !sleep_indicator.read()? {}

    const DATA_SIZE: usize = 10;
    sleep_pin.write(SLEEP)?;
    wait_sleep(&*sleep_indicator, &*uart, opts.timeout)?;
    /* Test the spi dev in sleep with the SD0 in high. */
    let mut buf = [0x55u8; DATA_SIZE];
    spi.run_transaction(&mut [Transfer::Write(&[0x55; 1]), Transfer::Read(&mut buf)])?;
    assert_eq!(&buf, &[0xffu8; DATA_SIZE]);
    sleep_pin.write(AWAKE)?;
    wait_awake(&*sleep_indicator, &*uart, opts.timeout)?;

    sleep_pin.write(SLEEP)?;
    wait_sleep(&*sleep_indicator, &*uart, opts.timeout)?;
    /* Test the spi dev in sleep with the SD0 in low. */
    let mut buf = [0x55u8; DATA_SIZE];
    spi.run_transaction(&mut [Transfer::Write(&[0x55; 1]), Transfer::Read(&mut buf)])?;
    assert_eq!(&buf, &[0x00u8; DATA_SIZE]);
    sleep_pin.write(AWAKE)?;
    wait_awake(&*sleep_indicator, &*uart, opts.timeout)?;

    Ok(())
}

fn spi_wakeup_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let sleep_pin = transport.gpio_pin("IOA8")?;
    sleep_pin.set_mode(PinMode::PushPull)?;
    let sleep_indicator = transport.gpio_pin("IOA7")?;
    sleep_indicator.set_mode(PinMode::Input)?;
    sleep_indicator.set_pull_mode(PullMode::PullUp)?;
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    spi.set_max_speed(100_000)?;

    sleep_pin.write(SLEEP)?;
    wait_sleep(&*sleep_indicator, &*uart, opts.timeout)?;
    println!("Reading jedec id");
    // Should wakup when the cs goes low.
    let jdec_id = SpiFlash::read_jedec_id(&*spi, 5)?;
    assert_eq!(&jdec_id, &[0x17u8, 0x17, 0x74, 0x98, 0x22]);
    sleep_pin.write(AWAKE)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    transport.pin_strapping("RESET")?.apply()?;
    execute_test!(spi_sleep_test, &opts, &transport,);
    execute_test!(spi_wakeup_test, &opts, &transport,);

    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"PASS!\r\n")?),
        exit_failure: Some(Regex::new(r"FAIL:")?),
        ..Default::default()
    };

    // Now watch the console for the exit conditions.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    };

    Ok(())
}

fn wait_sleep(gpio: &dyn GpioPin, uart: &dyn Uart, timeout: Duration) -> Result<()> {
    let _ = UartConsole::wait_for(uart, r"SYNC: Sleeping\r\n", timeout)?;
    while gpio.read()? {}
    Ok(())
}

fn wait_awake(gpio: &dyn GpioPin, uart: &dyn Uart, timeout: Duration) -> Result<()> {
    while !gpio.read()? {}
    let _ = UartConsole::wait_for(uart, r"SYNC: Awaked\r\n", timeout)?;
    Ok(())
}
