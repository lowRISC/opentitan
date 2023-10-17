// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use object::{Object, ObjectSymbol};
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::{MemRead32Req, MemReadReq, MemWrite32Req, MemWriteReq};
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

fn test_mem_word_commands(
    _opts: &Opts,
    test_word_address: u32,
    transport: &TransportWrapper,
) -> Result<()> {
    let uart = transport.uart("console")?;
    let read_value = MemRead32Req::execute(&*uart, test_word_address)?;
    assert!(read_value == 0xface1234_u32);

    let expected_value = 0x12345678_u32;
    MemWrite32Req::execute(&*uart, test_word_address, expected_value)?;
    let read_value = MemRead32Req::execute(&*uart, test_word_address)?;
    assert!(read_value == expected_value);
    Ok(())
}

fn test_mem_array_commands(
    _opts: &Opts,
    test_bytes_address: u32,
    transport: &TransportWrapper,
) -> Result<()> {
    let uart = transport.uart("console")?;
    let mut data: [u8; 256] = [0; 256];
    MemReadReq::execute(&*uart, test_bytes_address, data.as_mut_slice())?;
    let mut expected_value = Vec::<u8>::from_iter(0..=255);
    assert!(data.as_slice() == expected_value.as_slice());

    data.reverse();
    expected_value.reverse();
    MemWriteReq::execute(&*uart, test_bytes_address, expected_value.as_slice())?;
    MemReadReq::execute(&*uart, test_bytes_address, data.as_mut_slice())?;
    assert!(data.as_slice() == expected_value.as_slice());
    Ok(())
}

fn test_end(opts: &Opts, end_test_address: u32, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let end_test_value = MemRead32Req::execute(&*uart, end_test_address)?;
    assert!(end_test_value == 0);
    MemWrite32Req::execute(&*uart, end_test_address, /*value=*/ 1)?;
    let _ = UartConsole::wait_for(&*uart, r"PASS![^\r\n]*", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let elf_binary = fs::read(&opts.firmware_elf)?;
    let elf_file = object::File::parse(&*elf_binary)?;
    let mut symbols = HashMap::<String, u32>::new();
    for sym in elf_file.symbols() {
        symbols.insert(sym.name()?.to_owned(), sym.address() as u32);
    }
    let end_test_address = symbols
        .get("kEndTest")
        .expect("Provided ELF missing 'kEndTest' symbol");
    let test_word_address = symbols
        .get("kTestWord")
        .expect("Provided ELF missing 'kTestWord' symbol");
    let test_bytes_address = symbols
        .get("kTestBytes")
        .expect("Provided ELF missing 'kTestBytes' symbol");

    let transport = opts.init.init_target()?;
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;
    let _ = uart.clear_rx_buffer();

    execute_test!(
        test_mem_word_commands,
        &opts,
        *test_word_address,
        &transport
    );
    execute_test!(
        test_mem_array_commands,
        &opts,
        *test_bytes_address,
        &transport
    );
    execute_test!(test_end, &opts, *end_test_address, &transport);
    Ok(())
}
