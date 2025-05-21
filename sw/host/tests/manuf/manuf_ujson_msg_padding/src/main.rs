// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use clap::Parser;

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use ujson_lib::provisioning_data::{LcTokenHash, ManufCertgenInputs, PersoBlob, SerdesSha256Hash};
use ujson_lib::*;

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
    let sha256_hash = SerdesSha256Hash::recv(
        &spi_console,
        opts.timeout,
        /*quiet=*/ true,
        /*skip_crc=*/ true,
    )?;
    let lc_token_hash = LcTokenHash::recv(
        &spi_console,
        opts.timeout,
        /*quiet=*/ true,
        /*skip_crc=*/ true,
    )?;
    let certgen_inputs = ManufCertgenInputs::recv(
        &spi_console,
        opts.timeout,
        /*quiet=*/ true,
        /*skip_crc=*/ true,
    )?;
    let perso_blob = PersoBlob::recv(
        &spi_console,
        opts.timeout,
        /*quiet=*/ true,
        /*skip_crc=*/ true,
    )?;

    // Send the payloads back to the device.
    let sha256_hash_str =
        sha256_hash.send_with_padding(&spi_console, SERDES_SHA256_HASH_SERIALIZED_MAX_SIZE)?;
    let lc_token_hash_str =
        lc_token_hash.send_with_padding(&spi_console, LC_TOKEN_HASH_SERIALIZED_MAX_SIZE)?;
    let certgen_inputs_str =
        certgen_inputs.send_with_padding(&spi_console, MANUF_CERTGEN_INPUTS_SERIALIZED_MAX_SIZE)?;
    let perso_blob_str =
        perso_blob.send_with_padding(&spi_console, PERSO_BLOB_SERIALIZED_MAX_SIZE)?;

    // Check padded UJSON string sizes.
    assert_eq!(
        sha256_hash_str.len(),
        SERDES_SHA256_HASH_SERIALIZED_MAX_SIZE
    );
    assert_eq!(lc_token_hash_str.len(), LC_TOKEN_HASH_SERIALIZED_MAX_SIZE);
    assert_eq!(
        certgen_inputs_str.len(),
        MANUF_CERTGEN_INPUTS_SERIALIZED_MAX_SIZE
    );
    assert_eq!(perso_blob_str.len(), PERSO_BLOB_SERIALIZED_MAX_SIZE);

    Ok(())
}
