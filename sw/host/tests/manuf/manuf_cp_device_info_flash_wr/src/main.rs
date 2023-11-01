// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::{anyhow, Result};
use clap::Parser;
use regex::Regex;

use opentitanlib::app::TransportWrapper;
use opentitanlib::backend;
use opentitanlib::dif::lc_ctrl::DifLcCtrlState;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    /// LC state to transition to from TEST_UNLOCKED*.
    #[arg(long, value_parser = DifLcCtrlState::parse_lc_state_str, default_value = "prod")]
    target_lc_state: DifLcCtrlState,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn manuf_cp_device_info_flash_wr(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Set CPU TAP straps, reset, and connect to the JTAG interface.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let mut jtag = opts.init.jtag_params.create(transport)?;
    jtag.connect(JtagTap::RiscvTap)?;

    // Reset and halt the CPU to ensure we are in a known state, and clear out any ROM messages
    // printed over the console.
    jtag.reset(/*run=*/ false)?;
    let uart = transport.uart("console")?;
    uart.clear_rx_buffer()?;

    // Load and execute the SRAM program that contains the test code.
    match opts
        .sram_program
        .load_and_execute(&mut *jtag, ExecutionMode::JumpAndWait(opts.timeout))?
    {
        ExecutionResult::ExecutionDone => {
            log::info!("SRAM program loaded and executed successfully.")
        }
        res => log::info!("SRAM program execution failed: {:?}.", res),
    }

    // Once the SRAM program has printed a message over the console, we can continue with a LC
    // transition initiated on the host side.
    let _ = UartConsole::wait_for(
        &*uart,
        r"Done. Perform an LC transition and run flash stage.",
        opts.timeout,
    )?;

    // Reset and halt the CPU to ensure we are in a known state again, clear out any ROM
    // messages printed over the console, and switch to the LC TAP to perform LC transition.
    jtag.reset(/*run=*/ false)?;
    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    jtag = opts.init.jtag_params.create(transport)?;
    jtag.connect(JtagTap::LcTap)?;

    // Issue an LC transition.
    const TEST_EXIT_TOKEN: [u32; 4] = [0x11111111, 0x11111111, 0x11111111, 0x11111111];
    // After the transition, the device will be in a production state but the flash
    // is empty so it will reboot constantly and we will not be able to get a JTAG
    // connection. Instead, the program that we bootstrap will check that the transition
    // was done correctly.
    trigger_lc_transition(
        transport,
        jtag,
        opts.target_lc_state,
        Some(TEST_EXIT_TOKEN),
        /*use_external_clk=*/ true,
        opts.init.bootstrap.options.reset_delay,
        /*reset_tap_straps=*/ None,
    )?;

    // Bootstrap test program into flash and wait for test status pass over the UART.
    uart.clear_rx_buffer()?;
    opts.init.bootstrap.init(transport)?;

    // Reset chip, run flash stage, and wait for test status pass over the UART.
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

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    // We call the below functions, instead of calling `opts.init.init_target()` since we do not
    // want to perform bootstrap yet.
    let transport = backend::create(&opts.init.backend_opts)?;
    transport.apply_default_configuration()?;
    InitializeTest::print_result("load_bitstream", opts.init.load_bitstream.init(&transport))?;

    execute_test!(manuf_cp_device_info_flash_wr, &opts, &transport);

    Ok(())
}
