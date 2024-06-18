// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::io::{BufReader, Read};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::{MemRead32Req, MemWriteReq};
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
    expected_data: Vec<u8>,
    uart_idx: u8,
    uart_idx_addr: u32,
    baud_rate_addr: u32,
    test_phase_addr: u32,
}

#[repr(u8)]
enum TestPhase {
    _Init,
    _Cfg,
    Send,
    Recv,
    _Done,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let elf_file = fs::read(&opts.firmware_elf).context("failed to read ELF")?;
    let object = object::File::parse(elf_file.as_ref()).context("failed to parse ELF")?;

    let expected_data = test_utils::object::symbol_data(&object, "kSendData")?;

    let uart_idx_addr = test_utils::object::symbol_addr(&object, "uart_idx")?;
    let baud_rate_addr = test_utils::object::symbol_addr(&object, "baud_rate")?;
    let test_phase_addr = test_utils::object::symbol_addr(&object, "test_phase")?;

    let transport = opts.init.init_target()?;
    let uart_console = transport.uart("console")?;

    for uart_idx in 0..4 {
        transport.reset_target(Duration::from_millis(500), true)?;

        let test_data = TestData {
            expected_data: expected_data.clone(),
            uart_idx,
            uart_idx_addr,
            baud_rate_addr,
            test_phase_addr,
        };

        execute_test!(
            uart_baud_rate,
            &opts,
            &transport,
            &*uart_console,
            &test_data
        );
    }

    // Reset baud rate to the default.
    // HyperDebug doesn't seem to clear this properly between tests.
    let uart = transport.uart("dut")?;
    uart.set_baudrate(115200)?;
    uart.clear_rx_buffer()?;

    Ok(())
}

/// Send and receive data with a device's UART.
fn uart_baud_rate(
    opts: &Opts,
    transport: &TransportWrapper,
    console: &dyn Uart,
    test_data: &TestData,
) -> Result<()> {
    let TestData {
        expected_data,
        uart_idx,
        uart_idx_addr,
        baud_rate_addr,
        test_phase_addr,
    } = test_data;

    let uart = transport.uart("dut")?;

    UartConsole::wait_for(console, r"waiting for commands", opts.timeout)?;
    MemWriteReq::execute(console, *uart_idx_addr, &[*uart_idx])?;

    // Keep repeating the test for various Bauds until the device tells us it's
    // `PASS`ed.
    loop {
        let msg = UartConsole::wait_for(
            console,
            r"PASS![^\r\n]*|Starting test[^\n]*\n",
            opts.timeout,
        )?;

        if msg[0].as_str().contains("PASS") {
            break;
        }

        // Read the configured baud rate and configure our side of the UART.
        UartConsole::wait_for(console, r"waiting for commands", opts.timeout)?;
        let baud_rate = MemRead32Req::execute(console, *baud_rate_addr)?;
        uart.set_baudrate(baud_rate)?;
        uart.clear_rx_buffer()?;

        // Ask the device to send us some data.
        MemWriteReq::execute(console, *test_phase_addr, &[TestPhase::Send as u8])?;
        UartConsole::wait_for(console, r"Data sent[^\n]*\n", opts.timeout)?;

        log::info!("Reading data...");

        let mut data = vec![0u8; expected_data.len()];
        let mut buf_reader = BufReader::new(&*uart);
        buf_reader
            .read_exact(&mut data)
            .context("failed to read data")?;

        assert_eq!(data, *expected_data);

        // Ask the device to receive the data we send.
        MemWriteReq::execute(console, *test_phase_addr, &[TestPhase::Recv as u8])?;

        log::info!("Sending data...");
        uart.write(expected_data).context("failed to send data")?;
    }

    Ok(())
}
