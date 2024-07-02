// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::Parser;
use regex::Regex;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::BitbangEntry;
use opentitanlib::io::gpio::{GpioPin, PinMode, PullMode};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::{self, mem::MemWriteReq};
use opentitanlib::uart::console::{ExitStatus, UartConsole};
use std::borrow::Borrow;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

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

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

struct TestContext<'a> {
    backdoor_cpha: u32,
    backdoor_cpol: u32,
    backdoor_data: u32,
    gpio_pins: &'a [Rc<dyn GpioPin>],
    cpol: u8,
    cpha: u8,
}
const SPI_PIN_CS: u8 = 0;
const SPI_PIN_SCL: u8 = 1;
const SPI_PIN_D0: u8 = 2;
const SPI_PIN_D1: u8 = 3;

fn spi_host_config_test(opts: &Opts, transport: &TransportWrapper, ctx: &TestContext) -> Result<()> {
    let uart = transport.uart("console")?;
    let gpio_bitbanging = transport.gpio_bitbanging()?;

    const SAMPLES: usize = 5000;
    let mut samples = vec![0x00; SAMPLES];
    let output = &mut [0x7; SAMPLES];
    output[1] = 0x0f; // A rising edge on the D1 to indicate when the sampling started, which is helpfull when debugging.
    let waveform = Box::new([BitbangEntry::Both(output, &mut samples)]);

    UartConsole::wait_for(
        &*uart,
        r".*SiVal: waiting for commands.*?[^\r\n]*",
        opts.timeout,
    )?;
    MemWriteReq::execute(&*uart, ctx.backdoor_cpha, &[ctx.cpha])?;

    UartConsole::wait_for(
        &*uart,
        r".*SiVal: waiting for commands.*?[^\r\n]*",
        opts.timeout,
    )?;
    MemWriteReq::execute(&*uart, ctx.backdoor_cpol, &[ctx.cpol])?;

    UartConsole::wait_for(
        &*uart,
        r".*SiVal: waiting for commands.*?[^\r\n]*",
        opts.timeout,
    )?;
    MemWriteReq::execute(&*uart, ctx.backdoor_data, &[0xAB, 0xCD, 0xEF, 0xAB])?;
    gpio_bitbanging.run(
        &ctx.gpio_pins
            .iter()
            .map(Rc::borrow)
            .collect::<Vec<&dyn GpioPin>>(),
        Duration::from_micros(20),
        waveform,
    )?;

    let mut decoder = test_utils::bitbanging::spi::decoder::Decoder::<
        SPI_PIN_D0,
        SPI_PIN_D1,
        0, // D2, not in use.
        0, // D3, not in use.
        SPI_PIN_SCL,
        SPI_PIN_CS,
    > {
        cpol: ctx.cpol == 1,
        cpha: ctx.cpha == 1,
        data_mode: test_utils::bitbanging::spi::SpiDataMode::Single,
    };
    let decoded = decoder.run(samples.to_owned())?;
    assert_eq!(
        decoded,
        vec![0x06, 0x02, 0x00, 0x00, 0x00, 0xab, 0xcd, 0xef, 0xab, 0x05, 0x80,]
    );
    println!("decoded: {:?}", decoded);

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    println!("starting test");
    let transport = opts.init.init_target()?;

    /* Load the ELF binary and get the expect data.*/
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let object = object::File::parse(&*elf_binary)?;
    let mut ctx = TestContext {
        backdoor_cpha: test_utils::object::symbol_addr(&object, "backdoor_cpha")?,
        backdoor_cpol: test_utils::object::symbol_addr(&object, "backdoor_cpol")?,
        backdoor_data: test_utils::object::symbol_addr(&object, "backdoor_data")?,
        gpio_pins: &transport
            .gpio_pins(&["IOR10", "IOR11", "IOR12", "IOR13"].map(str::to_owned))?,
        cpol: 0,
        cpha: 0,
    };
    for pin in ctx.gpio_pins {
        pin.set_mode(PinMode::OpenDrain)?;
        pin.set_pull_mode(PullMode::PullUp)?;
    }
    ctx.cpol = 0;
    ctx.cpha = 0;
    execute_test!(spi_host_config_test, &opts, &transport, &ctx);
    ctx.cpol = 0;
    ctx.cpha = 1;
    execute_test!(spi_host_config_test, &opts, &transport, &ctx);
    ctx.cpol = 1;
    ctx.cpha = 0;
    execute_test!(spi_host_config_test, &opts, &transport, &ctx);
    ctx.cpol = 1;
    ctx.cpha = 1;
    execute_test!(spi_host_config_test, &opts, &transport, &ctx);

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
