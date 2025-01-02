// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::Parser;
use regex::Regex;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::tpm::{self, Driver};
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "TPM")]
    spi: String,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

fn tpm_read_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    transport.pin_strapping("SPI_TPM")?.apply()?;

    /* Wait sync message. */
    let _ = UartConsole::wait_for(&*uart, r"SYNC: Begin TPM Test\r\n", opts.timeout)?;
    let tpm = tpm::SpiDriver::new(spi, false)?;
    const SIZE: usize = 10;

    for _ in 0..10 {
        let test_data: Vec<u8> = (0..SIZE).map(|_| rand::random()).collect();
        tpm.write_register(tpm::Register::DATA_FIFO, &test_data)?;
        let _ = UartConsole::wait_for(&*uart, r"SYNC: Waiting Read\r\n", opts.timeout)?;
        let mut buffer = [0xFFu8; SIZE];
        tpm.read_register(tpm::Register::DATA_FIFO, &mut buffer)?;
        assert_eq!(buffer, &test_data[0..SIZE]);
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(tpm_read_test, &opts, &transport,);

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
