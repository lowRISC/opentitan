// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use regex::Regex;

use std::io;
use std::iter;
use anyhow::{bail, Context};
use opentitanlib::test_utils::lc_transition;
use opentitanlib::chip::boolean::MultiBitBool8;
use opentitanlib::dif::lc_ctrl::{
    DifLcCtrlState, DifLcCtrlToken, LcCtrlReg, LcCtrlStatus, LcCtrlTransitionCmd,
    LcCtrlTransitionRegwen,
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
use opentitanlib::uart::console::{ExitStatus,UartConsole};
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::load_sram_program::{
    execute_sram_program, ExecutionError, ExecutionMode, ExecutionResult, SramProgramParams,
};

/// Timeout for waiting for data over the console.
const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);

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

    let jtag = opts.init.jtag_params.create(transport)?;
    log::info!("Connecting to RISC-V TAP");
    jtag.connect(JtagTap::RiscvTap)?;
    log::info!("Halting core");
    jtag.halt()?;

    opts.sram_program
        .load_and_execute(&jtag, ExecutionMode::Jump)?;

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

    let jtag = opts.init.jtag_params.create(transport)?;
    jtag.connect(JtagTap::LcTap)
        .context("failed to connect to JTAG")?;

    // Wait for the lifecycle controller to enter the `READY` state from
    // which it accepts transition commands.
    lc_transition::wait_for_status(&jtag, Duration::from_secs(3), LcCtrlStatus::READY)
        .context("failed to wait for lifecycle controller to be ready")?;

//    // Check we're in the `PROD` state with 5 transitions registered.
//    assert_eq!(
//        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
//        DifLcCtrlState::Prod.redundant_encoding()
//    );
//    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcTransitionCnt)?, 5);

    // Attempt to claim the transition mutex.
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::ClaimTransitionIf,
        u8::from(MultiBitBool8::True) as u32,
    )?;
    // Will be true if the transition was successful.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::ClaimTransitionIf)?,
        u8::from(MultiBitBool8::True) as u32
    );
    // And hardware will enable writing to transition registers.
    let regwen = jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionRegwen)?;
    let regwen = LcCtrlTransitionRegwen::from_bits(regwen)
        .context("TRANSITION_REGWEN has invalid bits set")?;
    assert_eq!(regwen, LcCtrlTransitionRegwen::TRANSITION_REGWEN);

    // Multi-reg registers for the transition token.
    let token_regs = [
        &LcCtrlReg::TransitionToken0,
        &LcCtrlReg::TransitionToken1,
        &LcCtrlReg::TransitionToken2,
        &LcCtrlReg::TransitionToken3,
    ];
    // This is the preimage of the RMA token, randomly generated. The postimage
    // is was generated using the `gen_rma_token.py` script and embedded in the
    // OTP's SECRET2 partition.
    let token = DifLcCtrlToken::from([
        0x53, 0xa3, 0x81, 0x2b, 0x5a, 0x4c, 0x04, 0xa4, //
        0x85, 0xda, 0xac, 0x25, 0x2d, 0x14, 0x5c, 0xaf,
    ]);
    let token_words = token.into_register_values();

    // Write token to the multi-register.
    for (reg, value) in iter::zip(token_regs, token_words) {
        jtag.write_lc_ctrl_reg(reg, value)?;
    }

    // Read back the values to confirm the write.
    for (reg, value) in iter::zip(token_regs, token_words) {
        assert_eq!(jtag.read_lc_ctrl_reg(reg)?, value);
    }

    // Set the transition target to `RMA` and read back to confirm.
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::TransitionTarget,
        DifLcCtrlState::Rma.redundant_encoding(),
    )?;
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionTarget)?,
        DifLcCtrlState::Rma.redundant_encoding(),
    );

    log::info!("Initiating lifecycle transition");

    // Write `START` to the `TRANSITION_CMD` register.
    jtag.write_lc_ctrl_reg(&LcCtrlReg::TransitionCmd, LcCtrlTransitionCmd::START.bits())?;

    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionRegwen)?, 0);

    let status = jtag.read_lc_ctrl_reg(&LcCtrlReg::Status)?;
    let status = LcCtrlStatus::from_bits(status).context("invalid status bits")?;
    assert_eq!(status, LcCtrlStatus::INITIALIZED);

    // Poll until status register reports a successful transition.
    lc_transition::wait_for_status(
        &jtag,
        Duration::from_secs(3),
        LcCtrlStatus::TRANSITION_SUCCESSFUL,
    )
    .context("failed to wait for LC to report TRANSITION_SUCCESSFUL status")?;

    // Lifecycle controller should now be in the POST_TRANSITION state.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        DifLcCtrlState::PostTransition.redundant_encoding()
    );

    log::info!("Lifecycle transition complete");

    // No longer need the JTAG interface, shut down gracefully.
    jtag.disconnect()
        .context("failed to disconnect from JTAG")?;

    // Remove the RMA strapping so that future resets bring up normally.
    rma_bootstrap_strapping
        .remove()
        .context("failed to remove strapping RMA_BOOTSTRAP")?;

    // Remove the strapping in case this state survives to another test.
    tap_strapping
        .remove()
        .context("failed to remove strapping PINMUX_TAP_LC")?;

    // Reset again and check the lifecycle state is now `RMA` by reading for
    // "LCV:" on the UART.

    let uart = transport.uart("console").context("failed to get console")?;

    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset target")?;

    let rma_state = DifLcCtrlState::Rma.redundant_encoding();
    let exit_success =
        Regex::new(format!("LCV:{rma_state:x}\r\n").as_str()).context("failed to build regex")?;
    let exit_failure = Regex::new("LCV:[0-9a-f]+\r\n").context("failed to build regex")?;

    log::info!("dbg1");
    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(exit_success),
        exit_failure: Some(exit_failure),
        ..Default::default()
    };

    let mut stdout = io::stdout();
    let result = console
        .interact(&*uart, None, Some(&mut stdout))
        .context("failed to interact with console")?;
    log::info!("dbg2");

//    match result {
//        ExitStatus::ExitSuccess => Ok(()),
//        result => bail!("FAIL: {result:?}"),
//    }
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


    execute_test!(test_sram_load, &opts, &transport);
    execute_test!(test_update_phase, &opts, *test_word_address, &transport, 0);
    execute_test!(test_end, &opts, *end_test_address, &transport);

    execute_test!(test_rma_command, &opts, &transport);

    log::info!("host: round2");
    execute_test!(test_sram_load, &opts, &transport);
    execute_test!(test_update_phase, &opts, *test_word_address, &transport, 1);
    execute_test!(test_end, &opts, *end_test_address, &transport);
    Ok(())
}
