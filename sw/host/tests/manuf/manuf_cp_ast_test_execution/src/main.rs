// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use regex::Regex;
use std::rc::Rc;
use std::time::Duration;

use anyhow::{anyhow, bail, Context, Result};
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{Jtag, JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,
    #[structopt(flatten)]
    jtag: JtagParams,
    #[structopt(flatten)]
    sram_program: SramProgramParams,
    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "600s",
        help = "Console receive timeout",
    )]
    timeout: Duration,
}

fn connect_riscv_jtag(opts: &Opts, transport: &TransportWrapper) -> Result<Rc<dyn Jtag>> {
    // Set straps for the CPU TAP and reset.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .apply()
        .context("failed to apply RISCV TAP strapping")?;
    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset")?;

    let jtag = transport.jtag(&opts.jtag)?;
    log::info!("Connecting to RISC-V TAP");
    jtag.connect(JtagTap::RiscvTap)?;
    // This test is supposed to be run with ROM execution disabled but just in case
    // we reset the core to make sure we are in a known state. This disables the watchdog.
    jtag.reset(false)?;
    log::info!("target reset and halted");
    Ok(jtag)
}

fn manuf_cp_ast_text_execution_write_otp(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let jtag = connect_riscv_jtag(opts, transport)?;
    let uart = transport.uart("console")?;
    // Make sure to remove any messages from the ROM.
    uart.clear_rx_buffer()?;
    // Load SRAM program to write the OTP.
    match opts
        .sram_program
        .load_and_execute(&jtag, ExecutionMode::Jump)?
    {
        ExecutionResult::Executing => log::info!("program successfully started"),
        res => bail!("program execution failed: {:?}", res),
    }
    // TODO read OTP here
    // Wait for test status pass over the UART.
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"PASS.*\n")?),
        exit_failure: Some(Regex::new(r"(FAIL|FAULT).*\n")?),
        newline: true,
        ..Default::default()
    };
    let mut stdout = std::io::stdout();
    let result = console.interact(&*uart, None, Some(&mut stdout))?;
    jtag.disconnect()?;
    match result {
        ExitStatus::None | ExitStatus::CtrlC => Ok(()),
        ExitStatus::Timeout => {
            if console.exit_success.is_some() {
                Err(anyhow!("Console timeout exceeded"))
            } else {
                Ok(())
            }
        }
        ExitStatus::ExitSuccess => {
            log::info!(
                "ExitSuccess({:?})",
                console.captures(result).unwrap().get(0).unwrap().as_str()
            );
            Ok(())
        }
        ExitStatus::ExitFailure => {
            log::info!(
                "ExitFailure({:?})",
                console.captures(result).unwrap().get(0).unwrap().as_str()
            );
            Err(anyhow!("Matched exit_failure expression"))
        }
    }
}

fn manuf_cp_ast_text_execution_read_otp(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let jtag = connect_riscv_jtag(opts, transport)?;
    let uart = transport.uart("console")?;
    // Make sure to remove any messages from the ROM.
    uart.clear_rx_buffer()?;
    // TODO read OTP
    jtag.disconnect()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Part 1: write OTP using an SRAM program.
    execute_test!(manuf_cp_ast_text_execution_write_otp, &opts, &transport);
    // Part 2: verify OTP write using JTAG.
    execute_test!(manuf_cp_ast_text_execution_read_otp, &opts, &transport);

    Ok(())
}
