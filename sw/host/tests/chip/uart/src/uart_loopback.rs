// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::io::{BufReader, Read};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::Parser;
use object::read::File;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::MemWriteReq;
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

struct TestData {
    uart_idx: u8,
    uart_idx_addr: u32,
    test_phase_addr: u32,
}

#[repr(u8)]
enum TestPhase {
    _Cfg,
    Line,
    System,
    _Done,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let elf_file = fs::read(&opts.firmware_elf).context("failed to read ELF")?;
    let object: File = File::parse(elf_file.as_ref()).context("failed to parse ELF")?;

    let uart_idx_addr = test_utils::object::symbol_addr(&object, "uart_idx")?;
    let test_phase_addr = test_utils::object::symbol_addr(&object, "test_phase")?;

    let transport = opts.init.init_target()?;
    let uart_console = transport.uart("console")?;

    for uart_idx in 0..4 {
        transport.reset_target(Duration::from_millis(500), true)?;

        let test_data = TestData {
            uart_idx,
            uart_idx_addr,
            test_phase_addr,
        };

        execute_test!(uart_loopback, &opts, &transport, &*uart_console, &test_data);
    }

    Ok(())
}

/// Send and receive data with a device's UART.
fn uart_loopback(
    opts: &Opts,
    transport: &TransportWrapper,
    console: &dyn Uart,
    test_data: &TestData,
) -> Result<()> {
    const TEST_DATA: [u8; 14] = *b"Loopback test!";

    let uart = transport.uart("dut")?;
    std::thread::sleep(Duration::from_millis(100));
    uart.clear_rx_buffer()?;

    let TestData {
        uart_idx,
        uart_idx_addr,
        test_phase_addr,
    } = test_data;

    UartConsole::wait_for(console, r"waiting for commands", opts.timeout)?;
    MemWriteReq::execute(console, *uart_idx_addr, &[*uart_idx])?;

    UartConsole::wait_for(console, r"waiting for commands", opts.timeout)?;
    MemWriteReq::execute(console, *test_phase_addr, &[TestPhase::Line as u8])?;
    log::info!("Starting line loopback test");

    log::info!("Sending data...");
    uart.write(&TEST_DATA).context("failed to send data")?;

    log::info!("Reading data...");
    let mut received_data = [0u8; TEST_DATA.len()];
    let mut buf_reader = BufReader::new(&*uart);
    buf_reader
        .read_exact(&mut received_data)
        .context("failed to read data")?;

    assert_eq!(received_data, TEST_DATA);

    UartConsole::wait_for(console, r"waiting for commands", opts.timeout)?;
    MemWriteReq::execute(console, *test_phase_addr, &[TestPhase::System as u8])?;
    log::info!("Starting system loopback test");

    UartConsole::wait_for(console, r"PASS![^\r\n]*", opts.timeout)?;

    Ok(())
}
