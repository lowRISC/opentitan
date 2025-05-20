// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::ConsoleRecv;
use opentitanlib::uart::console::UartConsole;
use ujson_lib::provisioning_data::PersoBlob;

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

fn spi_device_console_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Setup the SPI console with the GPIO TX indicator pin.
    let spi = transport.spi(&opts.console_spi)?;
    let device_console_tx_ready_pin = &transport.gpio_pin("IOA5")?;
    device_console_tx_ready_pin.set_mode(PinMode::Input)?;
    device_console_tx_ready_pin.set_pull_mode(PullMode::None)?;
    let spi_console_device = SpiConsoleDevice::new(
        &*spi,
        Some(device_console_tx_ready_pin),
        /*ignore_frame_num=*/ false,
    )?;

    // Load the ELF binary and get the expect data.
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let object = object::File::parse(&*elf_binary)?;
    let data = test_utils::object::symbol_data(&object, "kTest4KbDataStr")?;
    let data_str = std::str::from_utf8(&data)?.trim_matches(char::from(0));

    // Wait for generic strings to be transmitted.
    for _ in 0..2 {
        // Receive simple string from the device.
        _ = UartConsole::wait_for_bytes(&spi_console_device, "ABC", opts.timeout)?;

        // Receive 4K of data from the device.
        _ = UartConsole::wait_for_bytes(&spi_console_device, data_str, opts.timeout)?;
    }

    // Receive the UJSON string transmitted and verify its contents.
    let perso_blob = PersoBlob::recv(&spi_console_device, opts.timeout, true, false)?;
    for i in 0..perso_blob.body.len() {
        assert_eq!(perso_blob.body[i], (i % 256) as u8);
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    execute_test!(spi_device_console_test, &opts, &transport);
    Ok(())
}
