// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::io::Read;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::{Parity, Uart};
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

#[repr(u8)]
enum TestPhase {
    _Cfg,
    Send,
    Recv,
    RecvErr,
    BreakErr,
    _BreakErrDone,
}

struct TestData<'a> {
    uart_id: u8,
    parity: Parity,
    tx_rx_data: &'a [u8],
    parity_addr: u32,
    uart_id_addr: u32,
    test_phase_addr: u32,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let elf_file = fs::read(&opts.firmware_elf).context("failed to read ELF")?;
    let object = object::File::parse(elf_file.as_ref()).context("failed to parse ELF")?;

    let tx_rx_data = test_utils::object::symbol_data(&object, "kUartData")?;
    let parity_addr = test_utils::object::symbol_addr(&object, "parity")?;
    let uart_id_addr = test_utils::object::symbol_addr(&object, "uart_idx")?;
    let test_phase_addr = test_utils::object::symbol_addr(&object, "test_phase")?;

    let transport = opts.init.init_target()?;
    let uart_console = transport.uart("console")?;

    // Test all four UARTs with both parities.
    for uart_id in 0..4 {
        for parity in [Parity::Odd, Parity::Even, Parity::None] {
            transport.reset_target(Duration::from_millis(500), true)?;

            let test_data = TestData {
                uart_id,
                parity,
                tx_rx_data: &tx_rx_data,
                parity_addr,
                uart_id_addr,
                test_phase_addr,
            };

            execute_test!(
                uart_parity_break,
                &opts,
                &transport,
                &*uart_console,
                &test_data
            );
        }
    }

    Ok(())
}

/// Send and receive data with a device's UART checking that the parity matches.
/// Some data is then sent with the incorrect parity.
fn uart_parity_break(
    opts: &Opts,
    transport: &TransportWrapper,
    console: &dyn Uart,
    test_data: &TestData,
) -> Result<()> {
    let TestData {
        uart_id,
        parity,
        tx_rx_data,
        parity_addr,
        uart_id_addr,
        test_phase_addr,
    } = test_data;

    // Convert parity to the values that the UART DIF expects.
    let dif_parity = match parity {
        Parity::Odd => 0,
        Parity::Even => 1,
        Parity::None => 2,
    };

    // Configure the UART under test and the parity to use.
    UartConsole::wait_for(console, r"waiting for commands\r\n", opts.timeout)?;
    MemWriteReq::execute(console, *parity_addr, &[dif_parity])?;
    MemWriteReq::execute(console, *uart_id_addr, &[*uart_id])?;

    // Connect to the UART once configured.
    UartConsole::wait_for(console, r"UART\d configured", opts.timeout)?;
    let uart = transport.uart("dut")?;
    // NOTE: for some reason setting HyperDebug's parity causes it to invent
    // a NULL byte which doesn't exist on the UART lines. Sleep for the USB
    // timeout (so that the byte arrives at the host) and then clear the buf.
    uart.set_parity(*parity).context("failed to set parity")?;
    uart.clear_rx_buffer()?;

    // Tell the device to send us some data and check it.
    UartConsole::wait_for(console, r"waiting for commands\r\n", opts.timeout)?;
    MemWriteReq::execute(console, *test_phase_addr, &[TestPhase::Send as u8])?;

    log::info!("Reading data...");
    let mut received_data = vec![0u8; tx_rx_data.len()];
    uart.as_ref()
        .read_exact(&mut received_data)
        .context("failed to read data")?;

    assert_eq!(&received_data, tx_rx_data);

    // Tell the device to receive some correct data.
    UartConsole::wait_for(console, r"waiting for commands\r\n", opts.timeout)?;
    MemWriteReq::execute(console, *test_phase_addr, &[TestPhase::Recv as u8])?;

    log::info!("Sending data...");
    uart.write(tx_rx_data).context("failed to send data")?;

    if *parity != Parity::None {
        // Tell the device to receive some data with the wrong parity.
        UartConsole::wait_for(console, r"waiting for commands\r\n", opts.timeout)?;
        MemWriteReq::execute(console, *test_phase_addr, &[TestPhase::RecvErr as u8])?;

        let other_parity = match parity {
            Parity::Odd => Parity::Even,
            Parity::Even => Parity::Odd,
            Parity::None => unimplemented!(),
        };
        uart.set_parity(other_parity)
            .context("failed to set parity")?;
        uart.write(&[0xff]).context("failed to send data")?;
    }

    for _ in 0..4 {
        // Sync with the device.
        UartConsole::wait_for(console, r"waiting for commands\r\n", opts.timeout)?;
        MemWriteReq::execute(console, *test_phase_addr, &[TestPhase::BreakErr as u8])?;

        // At 115200 baud each character spans ~800us. A 16 character break takes
        // ~14ms. We sleep for long enough that all the break levels will trigger.
        uart.set_break(true).context("failed to set break")?;
        std::thread::sleep(Duration::from_millis(15));
        uart.set_break(false).context("failed to unset break")?;
    }

    // The device will tell us whether or not the data with the wrong parity
    // was received okay.
    UartConsole::wait_for(console, r"PASS![^\r\n]*", opts.timeout)?;
    Ok(())
}
