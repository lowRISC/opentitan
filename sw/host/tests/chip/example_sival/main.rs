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
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::{MemRead32Req, MemWrite32Req};
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

/* This matches the phases in example_sival.c */
#[repr(u32)]
enum Phase {
    /* Wait for host to move to next phase. */
    WaitHost1 = 0,
    /* Wait for device to move to next phase. */
    WaitDevice1 = 1,
    /* Wait for host to move to next phase. */
    WaitHost2 = 2,
    /* Test finished. */
    TestDone = 3,
}

/* Wait for the device to be ready to receice ujson message,
 * read the content of the `kPhase` variable on the device
 * and check that it matches the expected phase. Then set the
 * value of this variable to a new value. */
fn check_and_set_phase(
    uart: &dyn Uart,
    phase_address: u32,
    check_phase: Phase,
    set_phase: Phase,
) -> Result<()> {
    let phase_value = MemRead32Req::execute(uart, phase_address)?;
    assert!(phase_value == check_phase as u32);
    MemWrite32Req::execute(uart, phase_address, set_phase as u32)?;
    Ok(())
}

fn example_test(opts: &Opts, uart: &dyn Uart, phase_address: u32) -> Result<()> {
    /* Wait for device to be ready and change phase. */
    check_and_set_phase(uart, phase_address, Phase::WaitHost1, Phase::WaitDevice1)?;
    /* Wait for device to be ready and change phase. */
    check_and_set_phase(uart, phase_address, Phase::WaitHost2, Phase::TestDone)?;
    /* Wait for test to end. */
    let _ = UartConsole::wait_for(uart, r"PASS![^\r\n]*", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    /* Load the ELF binary and get the address of the `kPhase` variable
     * in example_sival.c */
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let elf_file = object::File::parse(&*elf_binary)?;
    let mut symbols = HashMap::<String, u32>::new();
    for sym in elf_file.symbols() {
        symbols.insert(sym.name()?.to_owned(), sym.address() as u32);
    }
    let phase_address = symbols
        .get("kPhase")
        .expect("Provided ELF missing 'kPhase' symbol");

    /* Initialize transport and wait until the test starts running */
    let transport = opts.init.init_target()?;
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(example_test, &opts, &*uart, *phase_address,);
    Ok(())
}
