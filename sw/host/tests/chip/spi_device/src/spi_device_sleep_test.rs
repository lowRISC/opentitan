// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::Parser;
use regex::Regex;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::spi::Transfer;
use opentitanlib::spiflash::SpiFlash;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "BOOTSTRAP")]
    spi: String,
}

fn spi_sleep_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    const DATA_SIZE: usize = 10;

    /* Test the spi dev in sleep with the SD0 in high. */
    let _ = UartConsole::wait_for(&*uart, r"SYNC: Entering lowpower mode\r\n", opts.timeout)?;
    let mut buf = [0x55u8; DATA_SIZE];
    spi.run_transaction(&mut [Transfer::Write(&[0x55; 1]), Transfer::Read(&mut buf)])?;
    assert_eq!(&buf, &[0xffu8; DATA_SIZE]);
    let _ = UartConsole::wait_for(&*uart, r"SYNC: Wakening up\r\n", opts.timeout)?;

    /* Test the spi dev in sleep with the SD0 in low. */
    let _ = UartConsole::wait_for(&*uart, r"SYNC: Entering lowpower mode\r\n", opts.timeout)?;
    let mut buf = [0x55u8; DATA_SIZE];
    spi.run_transaction(&mut [Transfer::Write(&[0x55; 1]), Transfer::Read(&mut buf)])?;
    assert_eq!(&buf, &[0x00u8; DATA_SIZE]);
    let _ = UartConsole::wait_for(&*uart, r"SYNC: Wakening up\r\n", opts.timeout)?;

    Ok(())
}

fn spi_flash_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    let _ = UartConsole::wait_for(&*uart, r"SYNC: Flash mode\r\n", opts.timeout)?;
    let jdec_id = SpiFlash::read_jedec_id(&*spi, 5)?;

    assert_eq!(&jdec_id, &[0x17u8, 0x17, 0x74, 0x98, 0x22]);

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(spi_sleep_test, &opts, &transport,);
    execute_test!(spi_flash_test, &opts, &transport,);

    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"PASS!\r\n")?),
        exit_failure: Some(Regex::new(r"FAIL:")?),
        ..Default::default()
    };

    // Now watch the console for the exit conditions.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    };

    Ok(())
}
