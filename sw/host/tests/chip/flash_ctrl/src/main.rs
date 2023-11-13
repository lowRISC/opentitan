// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use regex::Regex;

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use object::{Object, ObjectSymbol};
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::{MemRead32Req, MemWrite32Req};
use opentitanlib::uart::console::UartConsole;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::load_sram_program::{
    execute_sram_program, ExecutionError, ExecutionMode, ExecutionResult, SramProgramParams,
};

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

    #[command(flatten)]
    sram_program: SramProgramParams,

}

//#[derive(Debug, Parser)]
//struct Opts2 {
//    #[command(flatten)]
//    init: InitializeTest,
//
//    #[command(flatten)]
//    sram_program: SramProgramParams,
//}


//fn test_update_phase(
//    _opts: &Opts,
//    test_word_address: u32,
//    transport: &TransportWrapper,
//    value: u32,
//) -> Result<()> {
//    let uart = transport.uart("console")?;
//    MemWrite32Req::execute(&*uart, test_word_address, value)?;
//    Ok(())
//}
//
//fn test_end(opts: &Opts, end_test_address: u32, transport: &TransportWrapper) -> Result<()> {
//    let uart = transport.uart("console")?;
//    let end_test_value = MemRead32Req::execute(&*uart, end_test_address)?;
//    assert!(end_test_value == 0);
//    MemWrite32Req::execute(&*uart, end_test_address, /*value=*/ 1)?;
//    let _ = UartConsole::wait_for(&*uart, r"PASS![^\r\n]*", opts.timeout)?;
//    Ok(())
//}

fn test_sram_load(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    //
    // Connect to the RISC-V TAP
    //
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let jtag = opts.init.jtag_params.create(transport)?;
    log::info!("Connecting to RISC-V TAP");
    jtag.connect(JtagTap::RiscvTap)?;
    log::info!("Halting core");
    jtag.halt()?;

    opts.sram_program
        .load_and_execute(&jtag, ExecutionMode::Jump)?;

    const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);
    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(Regex::new(
            r"sram_program\.c:\d+\] PC: 0x1000[0-2][0-9a-f]{3}, SRAM: \[0x10000000, 0x10020000\)",
        )?),
        ..Default::default()
    };
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    log::info!("result: {:?}", result);
    jtag.halt()?;
    jtag.disconnect()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_sram_load, &opts, &transport);

//    let opts = Opts::parse();
//    opts.init.init_logging();

  //  let elf_binary = fs::read(&opts.firmware_elf)?;
  //  let elf_file = object::File::parse(&*elf_binary)?;
  //  let mut symbols = HashMap::<String, u32>::new();
  //  for sym in elf_file.symbols() {
  //      symbols.insert(sym.name()?.to_owned(), sym.address() as u32);
  //  }
  //  let end_test_address = symbols
  //      .get("kEndTest")
  //      .expect("Provided ELF missing 'kEndTest' symbol");
  //  let test_word_address = symbols
  //      .get("kTestWord")
  //      .expect("Provided ELF missing 'kTestWord' symbol");
  //
  //  let transport = opts.init.init_target()?;
  //  let uart = transport.uart("console")?;
  //  uart.set_flow_control(true)?;
  //  let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;
  //  let _ = uart.clear_rx_buffer();
  //
  //  log::info!("word_address {:x}",test_word_address);
  //  execute_test!(
  //      test_update_phase,
  //      &opts,
  //      *test_word_address,
  //      &transport,
  //      33
  //  );
  //
  //  execute_test!(test_end, &opts, *end_test_address, &transport);

    Ok(())
}
