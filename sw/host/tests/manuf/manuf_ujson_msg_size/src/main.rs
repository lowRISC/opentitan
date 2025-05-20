// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
//use arrayvec::ArrayVec;
use clap::Parser;

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use ujson_lib::provisioning_data::{LcTokenHash, ManufCertgenInputs, PersoBlob, SerdesSha256Hash};

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

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "IOA5")]
    console_tx_indicator_pin: String,
}

fn main() -> Result<()> {
    // Load bitstream and bootstrap test.
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Initialize the console.
    let spi = transport.spi(&opts.console_spi)?;
    let device_console_tx_ready_pin = &transport.gpio_pin(&opts.console_tx_indicator_pin)?;
    device_console_tx_ready_pin.set_mode(PinMode::Input)?;
    device_console_tx_ready_pin.set_pull_mode(PullMode::None)?;
    let spi_console = SpiConsoleDevice::new(
        &*spi,
        Some(device_console_tx_ready_pin),
        /*ignore_frame_num=*/ false,
    )?;

    // Receive the payloads from the device.
    let sha256_hash = SerdesSha256Hash::recv(&spi_console, opts.timeout, /*quiet=*/ true)?;
    let lc_token_hash = LcTokenHash::recv(&spi_console, opts.timeout, /*quiet=*/ true)?;
    let certgen_inputs =
        ManufCertgenInputs::recv(&spi_console, opts.timeout, /*quiet=*/ true)?;
    let perso_blob = PersoBlob::recv(&spi_console, opts.timeout, /*quiet=*/ true)?;

    // Send the payloads back to the device.
    let sha256_hash_str = sha256_hash.send(&spi_console)?;
    let lc_token_hash_str = lc_token_hash.send(&spi_console)?;
    let certgen_inputs_str = certgen_inputs.send(&spi_console)?;
    let perso_blob_str = perso_blob.send(&spi_console)?;

    // Print UJSON payload sizes to the console.
    println!("Sha256Hash Size:         {} bytes", sha256_hash_str.len());
    println!("LcTokenHash Size:        {} bytes", lc_token_hash_str.len());
    println!(
        "ManufCertgenInputs Size: {} bytes",
        certgen_inputs_str.len()
    );
    println!("PersoBlob Size:          {} bytes", perso_blob_str.len());

    Ok(())
}
