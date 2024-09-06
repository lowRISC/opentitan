// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::Result;
use clap::Parser;
use object::{Object, ObjectSymbol};
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::{MemRead32Req, MemReadReq, MemWrite32Req, MemWriteReq};
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::uart::console::UartConsole;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;
use ujson_lib::provisioning_data::PersoBlob;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "60s")]
    timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "BOOTSTRAP")]
    console_spi: String,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

const SYNC_MSG: &str = r"SYNC:.*\r\n";

fn test_perso_blob_strcut(opts: &Opts, spi_console: &SpiConsoleDevice) -> Result<()> {
    UartConsole::wait_for(spi_console, SYNC_MSG, opts.timeout)?;
    let perso_blob = PersoBlob::recv(spi_console, opts.timeout, true)?;
    UartConsole::wait_for(spi_console, SYNC_MSG, opts.timeout)?;
    perso_blob.send(spi_console)?;
    Ok(())
}

fn test_mem_word_commands(
    _opts: &Opts,
    test_word_address: u32,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    let read_value = MemRead32Req::execute(spi_console, test_word_address)?;
    assert!(read_value == 0xface1234_u32);

    let expected_value = 0x12345678_u32;
    MemWrite32Req::execute(spi_console, test_word_address, expected_value)?;
    let read_value = MemRead32Req::execute(spi_console, test_word_address)?;
    assert!(read_value == expected_value);
    Ok(())
}

fn test_mem_array_commands(
    _opts: &Opts,
    test_bytes_address: u32,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    let mut data: [u8; 256] = [0; 256];
    MemReadReq::execute(spi_console, test_bytes_address, data.as_mut_slice())?;
    let mut expected_value = Vec::<u8>::from_iter(0..=255);
    assert!(data.as_slice() == expected_value.as_slice());

    data.reverse();
    expected_value.reverse();
    MemWriteReq::execute(spi_console, test_bytes_address, expected_value.as_slice())?;
    MemReadReq::execute(spi_console, test_bytes_address, data.as_mut_slice())?;
    assert!(data.as_slice() == expected_value.as_slice());
    Ok(())
}

fn test_end(opts: &Opts, end_test_address: u32, spi_console: &SpiConsoleDevice) -> Result<()> {
    let end_test_value = MemRead32Req::execute(spi_console, end_test_address)?;
    assert!(end_test_value == 0);
    MemWrite32Req::execute(spi_console, end_test_address, /*value=*/ 1)?;
    let _ = UartConsole::wait_for(spi_console, r"PASS![^\r\n]*", opts.timeout)?;
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
    let spi = transport.spi(&opts.console_spi)?;
    let spi_console_device = SpiConsoleDevice::new(&*spi)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(test_perso_blob_strcut, &opts, &spi_console_device);
    execute_test!(
        test_mem_word_commands,
        &opts,
        *test_word_address,
        &spi_console_device
    );
    execute_test!(
        test_mem_array_commands,
        &opts,
        *test_bytes_address,
        &spi_console_device
    );
    execute_test!(test_end, &opts, *end_test_address, &spi_console_device);
    Ok(())
}
