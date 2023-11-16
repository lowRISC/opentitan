// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;

use anyhow::Context;
use opentitanlib::test_utils::lc_transition;
use opentitanlib::dif::lc_ctrl::{
    DifLcCtrlState, DifLcCtrlToken, LcCtrlReg, LcCtrlStatus,
};

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
use opentitanlib::test_utils::load_sram_program::{ExecutionMode, SramProgramParams
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

fn test_update_phase(
    _opts: &Opts,
    test_word_address: u32,
    transport: &TransportWrapper,
    value: u32,
) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Starting [^\r\n]*", _opts.timeout)?;
    let _ = uart.clear_rx_buffer();
    MemWrite32Req::execute(&*uart, test_word_address, value)?;
    Ok(())
}

fn test_end(opts: &Opts, end_test_address: u32, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let end_test_value = MemRead32Req::execute(&*uart, end_test_address)?;
    assert!(end_test_value == 0);
    MemWrite32Req::execute(&*uart, end_test_address, /*value=*/ 1)?;
    let _ = UartConsole::wait_for(&*uart, r"test_end[^\r\n]*", opts.timeout)?;
    Ok(())
}

fn test_sram_load(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    //
    // Connect to the RISC-V TAP
    //
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    log::info!("Connecting to RISC-V TAP");
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    log::info!("Halting core");
    jtag.halt()?;

    opts.sram_program
        .load_and_execute(&mut *jtag, ExecutionMode::Jump)?;

    jtag.disconnect()?;
    Ok(())
}

fn test_rma_command(opts: &Opts, transport: &TransportWrapper) -> anyhow::Result<()> {
    let rma_bootstrap_strapping = transport.pin_strapping("RMA_BOOTSTRAP")?;
    let tap_strapping = transport.pin_strapping("PINMUX_TAP_LC")?;

    // Need to reset with `RMA_BOOTSTRAP` set.
    rma_bootstrap_strapping
        .apply()
        .context("failed to apply RMA_BOOTSTRAP strapping")?;

    // We keep `PINMUX_TAP_LC` set so that resets due to transition don't
    // disconnect us from the LC TAP.
    tap_strapping
        .apply()
        .context("failed to apply PINMUX_TAP_LC strapping")?;

    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset target")?;

    log::info!("Connecting to JTAG interface");

    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)
        .context("failed to connect to JTAG")?;

    let rma_unlock_token = DifLcCtrlToken::from([
        0x53, 0xa3, 0x81, 0x2b, 0x5a, 0x4c, 0x04, 0xa4, //
        0x85, 0xda, 0xac, 0x25, 0x2d, 0x14, 0x5c, 0xaf,
    ]);

    // Wait for the lifecycle controller to enter the `READY` state from
    // which it accepts transition commands.
    lc_transition::wait_for_status(&mut *jtag, Duration::from_secs(3), LcCtrlStatus::READY)
        .context("failed to wait for lifecycle controller to be ready")?;

    // Check we're in the `DEV` state with 5 transitions registered.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        DifLcCtrlState::Dev.redundant_encoding()
    );
    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcTransitionCnt)?, 5);

    lc_transition::trigger_lc_transition(
       transport,
       jtag,
       DifLcCtrlState::Rma,
       Some(rma_unlock_token.into_register_values()),
       /*use_external_clk=*/ false,
       opts.init.bootstrap.options.reset_delay,
       Some(JtagTap::LcTap),
    ).expect("failed to trigger transition to rma");

    // Remove the RMA strapping so that future resets bring up normally.
    rma_bootstrap_strapping
        .remove()
        .context("failed to remove strapping RMA_BOOTSTRAP")?;

    // Remove the strapping in case this state survives to another test.
    tap_strapping
        .remove()
        .context("failed to remove strapping PINMUX_TAP_LC")?;

    Ok(())
 }

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

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
        .get("kTestPhase")
        .expect("Provided ELF missing 'kTestWord' symbol");

    // 1st sram execution:
    // Upload c test to sram and update kTestPhase to kTestPhase0
    log::info!("host: round1");
    execute_test!(test_sram_load, &opts, &transport);
    execute_test!(test_update_phase, &opts, *test_word_address, &transport, 0);
    execute_test!(test_end, &opts, *end_test_address, &transport);

    // rma entry start by JtagTap::LcTap
    execute_test!(test_rma_command, &opts, &transport);

    // 2nd sram execution
    // Upload c test to sram and update kTestPhase to kTestPhase1
    log::info!("host: round2");
    execute_test!(test_sram_load, &opts, &transport);
    execute_test!(test_update_phase, &opts, *test_word_address, &transport, 1);
    execute_test!(test_end, &opts, *end_test_address, &transport);
    Ok(())
}
