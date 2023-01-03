// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use opentitanlib::dif::rstmgr::DifRstmgrResetInfo;
use regex::Regex;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "50s",
        help = "Console receive timeout",
    )]
    timeout: Duration,
}

/// Orchestrate iteration 1 of the rom_bootstrap_rma testpoint. This never
/// issues the life cycle RMA command. It verifies that the ROM times out on
/// spin cycles, automatically resets the device, and logs the expected reset
/// reasons.
fn test_no_rma_command(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let reset_delay = opts.init.bootstrap.options.reset_delay;
    let uart = transport.uart("console")?;

    log::info!("Applying RMA_BOOTSTRAP strapping...");
    transport.apply_pin_strapping("RMA_BOOTSTRAP")?;

    log::info!("Resetting target...");
    let clear_uart_rx = true;
    transport.reset_target(reset_delay, clear_uart_rx)?;

    log::info!("Removing RMA_BOOTSTRAP strapping...");
    transport.remove_pin_strapping("RMA_BOOTSTRAP")?;

    log::info!("Waiting for reset reasons on console...");

    // The `exit_success` and `exit_failure` patterns are tightly coupled with
    // sw/device/silicon_creator/rom/e2e/rom_e2e_bootstrap_rma_test.c.
    let expected_bitfield = u32::from(DifRstmgrResetInfo::Por) | u32::from(DifRstmgrResetInfo::Sw);
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(&format!(
            "reset_info_bitfield: 0x{expected_bitfield:x}\r\n"
        ))?),
        exit_failure: Some(Regex::new(r"reset_info_bitfield: 0x[0-9a-f]+\r\n")?),
        ..Default::default()
    };
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    };
    Ok(())
}

/// Orchestrate iteration 2 of the rom_bootstrap_rma testpoint. Issue the life
/// cycle RMA command and ensure the RMA transition is completed successfully.
fn test_rma_command(_opts: &Opts, _transport: &TransportWrapper) -> Result<()> {
    // TODO(lowRISC/opentitan#15677) Implement iteration 2 of rom_bootstrap_rma.
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_no_rma_command, &opts, &transport);
    execute_test!(test_rma_command, &opts, &transport);
    Ok(())
}
