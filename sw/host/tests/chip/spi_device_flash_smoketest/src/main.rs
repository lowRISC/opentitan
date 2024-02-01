// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::Parser;
use regex::Regex;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::eeprom::AddressMode;
use opentitanlib::spiflash::SpiFlash;
use opentitanlib::test_utils;
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

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

const SYNC_MSG: &str = r"SYNC:.*\r\n";

fn device_tx_rx_test(
    opts: &Opts,
    transport: &TransportWrapper,
    data: &[u8],
    address: u32,
) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    let mut flash = SpiFlash {
        // Double the flash size so we can test 3b and 4b addresses.
        size: 32 * 1024 * 1024,
        ..Default::default()
    };

    // Make sure we're in a mode appropriate for the address.
    let mode = if address < 0x1000000 {
        AddressMode::Mode3b
    } else {
        AddressMode::Mode4b
    };
    flash.set_address_mode(&*spi, mode)?;

    /* Wait sync message. */
    let _ = UartConsole::wait_for(&*uart, SYNC_MSG, opts.timeout)?;
    flash.program(&*spi, address, data)?;

    let mut buffer = vec![0xff; data.len()];
    flash.read(&*spi, address, &mut buffer)?;

    assert_eq!(buffer, data);

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    /* Load the ELF binary and get the expect data.*/
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let object = object::File::parse(&*elf_binary)?;

    let tx_data = test_utils::object::symbol_data(&object, "kSpiTxData")?;

    let transport = opts.init.init_target()?;
    execute_test!(device_tx_rx_test, &opts, &transport, &tx_data, 0x00);

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
