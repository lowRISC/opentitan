// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use clap::Parser;
use regex::Regex;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::execute_test;
use opentitanlib::io::console::ConsoleDevice;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "20s")]
    timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "BOOTSTRAP")]
    console_spi: String,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

const SYNC_MSG: &str = r"SYNC:.*\r\n";

fn spi_device_console_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"PASS.*\n")?),
        exit_failure: Some(Regex::new(r"(FAIL|FAULT).*\n")?),
        newline: true,
        ..Default::default()
    };
    let mut stdout = std::io::stdout();
    let spi = transport.spi(&opts.console_spi)?;

    let spi_console_device = SpiConsoleDevice::new(&*spi)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running [^\r\n]*", opts.timeout)?;

    /* Load the ELF binary and get the expect data.*/
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let object = object::File::parse(&*elf_binary)?;
    let mut data = test_utils::object::symbol_data(&object, "kTestStr")?;
    let mut data_str = std::str::from_utf8(&data)?.trim_matches(char::from(0));
    _ = UartConsole::wait_for(&spi_console_device, data_str, opts.timeout)?;
    log::info!("Sending test string to Device...");
    _ = UartConsole::wait_for(&spi_console_device, SYNC_MSG, opts.timeout)?;
    spi_console_device.console_write(&data)?;

    data = test_utils::object::symbol_data(&object, "kTest64bDataStr")?;
    data_str = std::str::from_utf8(&data)?.trim_matches(char::from(0));
    _ = UartConsole::wait_for(&spi_console_device, data_str, opts.timeout)?;
    log::info!("Sending 64B data to Device...");
    _ = UartConsole::wait_for(&spi_console_device, SYNC_MSG, opts.timeout)?;
    spi_console_device.console_write(&data)?;

    data = test_utils::object::symbol_data(&object, "kTest256bDataStr")?;
    data_str = std::str::from_utf8(&data)?.trim_matches(char::from(0));
    _ = UartConsole::wait_for(&spi_console_device, data_str, opts.timeout)?;
    log::info!("Sending 256 data to Device...");
    _ = UartConsole::wait_for(&spi_console_device, SYNC_MSG, opts.timeout)?;
    spi_console_device.console_write(&data)?;

    data = test_utils::object::symbol_data(&object, "kTest1KbDataStr")?;
    data_str = std::str::from_utf8(&data)?.trim_matches(char::from(0));
    // 1KB data will be sent twice.
    for _round in 0..2 {
        _ = UartConsole::wait_for(&spi_console_device, data_str, opts.timeout)?;
        log::info!("Sending 1KB data to Device...");
        _ = UartConsole::wait_for(&spi_console_device, SYNC_MSG, opts.timeout)?;
        spi_console_device.console_write(&data)?;
    }

    data = test_utils::object::symbol_data(&object, "kTest4KbDataStr")?;
    data_str = std::str::from_utf8(&data)?.trim_matches(char::from(0));
    _ = UartConsole::wait_for(&spi_console_device, data_str, opts.timeout)?;
    // 4KB data will be sent twice.
    for _round in 0..2 {
        log::info!("Sending 4KB data to Device...");
        _ = UartConsole::wait_for(&spi_console_device, SYNC_MSG, opts.timeout)?;
        spi_console_device.console_write(&data)?;
    }

    let result = console.interact(&spi_console_device, None, Some(&mut stdout))?;
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
    let transport = opts.init.init_target()?;
    execute_test!(spi_device_console_test, &opts, &transport);
    Ok(())
}
