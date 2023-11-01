// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use regex::Regex;
use std::time::Duration;

use anyhow::{anyhow, bail, Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::otp_ctrl::DaiParam;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{Jtag, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::otp_ctrl::OtpParam;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

/// This value is expected to be programmed into the OTP by the SRAM program.
const EXPECTED_DEVICE_ID: [u32; 8] = [
    0xdeadbeef, 0x12345678, 0xabcdef12, 0xcafebeef, 0x87654321, 0x21fedcba, 0xa1b2c3d4, 0xacdc4321,
];

fn connect_riscv_jtag<'t>(
    opts: &Opts,
    transport: &'t TransportWrapper,
) -> Result<Box<dyn Jtag + 't>> {
    // Set straps for the CPU TAP and reset.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .apply()
        .context("failed to apply RISCV TAP strapping")?;
    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset")?;

    let mut jtag = opts.init.jtag_params.create(transport)?;
    log::info!("Connecting to RISC-V TAP");
    jtag.connect(JtagTap::RiscvTap)?;

    // This test is supposed to be run with ROM execution disabled but just in case
    // we reset the core to make sure we are in a known state. This disables the watchdog.
    jtag.reset(false)?;
    log::info!("Target reset and halted.");

    Ok(jtag)
}

fn manuf_cp_ast_text_execution_write_otp(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let mut jtag = connect_riscv_jtag(opts, transport)?;

    // Make sure to remove any messages from the ROM.
    let uart = transport.uart("console")?;
    uart.clear_rx_buffer()?;

    // Load SRAM program to write the OTP.
    match opts
        .sram_program
        .load_and_execute(&mut *jtag, ExecutionMode::Jump)?
    {
        ExecutionResult::Executing => log::info!("program successfully started"),
        res => bail!("program execution failed: {:?}", res),
    }

    // Disconnect JTAG.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .remove()
        .context("failed to apply RISCV TAP strapping")?;
    jtag.disconnect()?;

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
    let mut jtag = connect_riscv_jtag(opts, transport)?;

    // Make sure to remove any messages from the ROM.
    let uart = transport.uart("console")?;
    uart.clear_rx_buffer()?;

    // Verify that the DEVICE_ID parameter in the OTP was correctly programmed. Although the SRAM
    // program is supposed to verify that, this adds redundancy to the test and avoids trusting
    // the SRAM program.
    let mut device_id =
        [0xffffffffu32; DaiParam::DEVICE_ID.size as usize / std::mem::size_of::<u32>()];
    OtpParam::read_param(&mut *jtag, DaiParam::DeviceId, &mut device_id)
        .context("failed to read back DEVICE_ID from OTP")?;
    assert_eq!(device_id, EXPECTED_DEVICE_ID);

    // Disconnect JTAG.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .remove()
        .context("failed to apply RISCV TAP strapping")?;
    jtag.disconnect()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Part 1: write OTP using an SRAM program.
    execute_test!(manuf_cp_ast_text_execution_write_otp, &opts, &transport);
    // Part 2: verify OTP write using JTAG.
    execute_test!(manuf_cp_ast_text_execution_read_otp, &opts, &transport);

    Ok(())
}
