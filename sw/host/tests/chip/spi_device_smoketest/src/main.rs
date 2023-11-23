// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::Parser;
use regex::Regex;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::spi::Transfer;
use opentitanlib::test_utils;
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

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

fn device_tx_watermark_test(
    opts: &Opts,
    transport: &TransportWrapper,
    tx_data: &[u8],
    rx_data: &[u8],
) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    /* Wait sync message. */
    let _ = UartConsole::wait_for(&*uart, r"SYNC: TX_FIFO READY\r\n", opts.timeout)?;

    let mut buf = vec![0u8; tx_data.len() - 1];
    // Due to the limitations of hyper310 (it does not support `Transfer::Both`) we first send one byte in order to
    // read the device rx FIFO.
    spi.run_transaction(&mut [Transfer::Write(&[tx_data[0]; 1]), Transfer::Read(&mut buf)])?;
    // Due to the limitations above, the first rx byte is lost in the write operation, so we need
    // to do this weird comparison.
    assert_eq!(&buf, &rx_data[1..]);
    Ok(())
}

fn device_rx_watermark_test(
    opts: &Opts,
    transport: &TransportWrapper,
    tx_data: &[u8],
) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    let _ = UartConsole::wait_for(&*uart, r"SYNC: RX_FIFO READY\r\n", opts.timeout)?;
    spi.run_transaction(&mut [Transfer::Write(tx_data)])
}

fn device_tx_underflow_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    /* Wait sync message. */
    let _ = UartConsole::wait_for(&*uart, r"SYNC: TX_FIFO UNDERFLOW READY\r\n", opts.timeout)?;
    spi.run_transaction(&mut [Transfer::Write(&[0xAA; 2])])
}

fn device_rx_full_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    /* Wait sync message. */
    let _ = UartConsole::wait_for(&*uart, r"SYNC: RX_FIFO FULL READY\r\n", opts.timeout)?;
    spi.run_transaction(&mut [Transfer::Write(&[0xAB; 1024])])
}

fn device_rx_overflow_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    /* Wait sync message. */
    let _ = UartConsole::wait_for(&*uart, r"SYNC: RX_FIFO OVERFLOW READY\r\n", opts.timeout)?;
    spi.run_transaction(&mut [Transfer::Write(&[0xB5; 64])])
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    /* Load the ELF binary and get the expect data.*/
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let object = object::File::parse(&*elf_binary)?;

    let spi_device_rx_data = test_utils::object::symbol_data(&object, "spi_device_tx_data")?;
    let spi_device_tx_data = test_utils::object::symbol_data(&object, "exp_spi_device_rx_data")?;

    let transport = opts.init.init_target()?;
    execute_test!(
        device_tx_watermark_test,
        &opts,
        &transport,
        &spi_device_tx_data,
        &spi_device_rx_data
    );

    execute_test!(
        device_rx_watermark_test,
        &opts,
        &transport,
        &spi_device_tx_data
    );

    execute_test!(device_tx_underflow_test, &opts, &transport);

    execute_test!(device_rx_full_test, &opts, &transport);

    execute_test!(device_rx_overflow_test, &opts, &transport);

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
