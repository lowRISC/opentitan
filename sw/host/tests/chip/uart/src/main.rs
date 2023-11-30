// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::io::{BufRead, BufReader, Read};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::execute_test;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Path to the ELF file being tested on the device.
    #[arg(long)]
    firmware_elf: PathBuf,
}

struct TxRxData {
    rx_data: Vec<u8>,
    tx_data: Vec<u8>,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;

    let spi = transport.spi("BOOTSTRAP")?;
    let console = SpiConsoleDevice::new(&*spi);

    let elf_file = fs::read(&opts.firmware_elf).context("failed to read ELF")?;
    let object = object::File::parse(elf_file.as_ref()).context("failed to parse ELF")?;

    let tx_rx_data = TxRxData {
        rx_data: test_utils::object::symbol_data(&object, "kExpUartRxData")?,
        tx_data: test_utils::object::symbol_data(&object, "kUartTxData")?,
    };

    execute_test!(uart_tx_rx, &opts, &transport, &console, &tx_rx_data);

    Ok(())
}

/// Send and receive data with a device's UART.
fn uart_tx_rx(
    opts: &Opts,
    transport: &TransportWrapper,
    console: &SpiConsoleDevice,
    tx_rx_data: &TxRxData,
) -> Result<()> {
    let uart = transport.uart("console")?;
    UartConsole::wait_for(console, r"Executing the test", opts.timeout)?;

    log::info!("Sending data...");
    uart.write(&tx_rx_data.rx_data)
        .context("failed to send data")?;

    // Read UART until the 0xff byte to skip ROM identification messages.
    let mut buf_reader = BufReader::new(&*uart);
    buf_reader
        .read_until(0xff, &mut Vec::new())
        .context("failed to read until 0xff marker byte")?;

    log::info!("Reading data...");
    let mut tx_data = vec![0u8; tx_rx_data.tx_data.len() - 1];

    buf_reader
        .read_exact(&mut tx_data)
        .context("failed to read data")?;

    assert_eq!(tx_data, &tx_rx_data.tx_data.as_slice()[1..]);

    log::info!("Sending a chun of data larget than the FIFO...");
    let too_much_data = vec![0xff; tx_rx_data.tx_data.len() + 1];
    uart.write(&too_much_data)
        .context("failed to write too much data")?;

    UartConsole::wait_for(console, r"PASS![^\r\n]*", opts.timeout)?;

    Ok(())
}
