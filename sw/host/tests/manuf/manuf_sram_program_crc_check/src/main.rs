// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::{bail, Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::{
    execute_sram_program, ExecutionError, ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::uart::console::UartConsole;

// use top_earlgrey::top_earlgrey;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,
}

fn test_sram_load(opts: &Opts, transport: &TransportWrapper, corrupt: bool) -> Result<()> {
    let uart = transport.uart("console")?;
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

    // Load program on the device.
    let sram_prog_info = opts.sram_program.load(&mut *jtag)?;

    // Corrupt program if asked to: mModify a random word in the code, not too close to the
    // starting point so that the CRT can still verify the CRC.
    if corrupt {
        let mut sram_content = [0u8];
        let tweak_addr = sram_prog_info.entry_point + 1000;
        log::info!("Corrupt SRAM program at address {:x}", tweak_addr);
        jtag.read_memory(tweak_addr, &mut sram_content)?;
        sram_content[0] ^= 0xff;
        jtag.write_memory(tweak_addr, &sram_content)?;
    }

    // Execute and check execution status.
    let exec_res = execute_sram_program(
        &mut *jtag,
        &sram_prog_info,
        ExecutionMode::JumpAndWait(Duration::from_secs(5)),
    )?;
    match exec_res {
        ExecutionResult::ExecutionDone => {
            if corrupt {
                bail!("SRAM program finished successfully but expected a CRC failure")
            } else {
                log::info!("SRAM program finished successfully")
            }
        }
        ExecutionResult::ExecutionError(err) => match err {
            ExecutionError::CrcMismatch if corrupt => {
                log::info!("SRAM program correctly reported a CRC mismatch")
            }
            _ => bail!("SRAM program execution failed with {:?}", err),
        },
        _ => {
            bail!(
                "SRAM program execution failed with unexpected result {:?}",
                exec_res
            )
        }
    }

    // If the program was not corrupted, make sure that it printed the expected message.
    if !corrupt {
        const CONSOLE_TIMEOUT: Duration = Duration::from_secs(1);
        let _ = UartConsole::wait_for(
            &*uart,
            r"sram_empty_functest\.c:\d+\] hello.",
            CONSOLE_TIMEOUT,
        )
        .context("SRAM program did not print 'hello' in time")?;
    }

    jtag.halt()?;
    jtag.disconnect()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // First test is normal.
    execute_test!(test_sram_load, &opts, &transport, false);
    // Second test we try to corrupt the data.
    execute_test!(test_sram_load, &opts, &transport, true);

    Ok(())
}
