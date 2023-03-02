// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::spiflash::SpiFlash;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::spi_passthru::ConfigJedecId;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "600s",
        help = "Console receive timeout",
    )]
    timeout: Duration,

    #[structopt(
        long,
        default_value = "BOOTSTRAP",
        help = "Name of the debugger's SPI interface"
    )]
    spi: String,
}

fn test_jedec_id(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let config = ConfigJedecId {
        device_id: 0x1234,
        manufacturer_id: 0x56,
        continuation_code: 0x7f,
        continuation_len: 3,
    };
    config.execute(&*uart)?;

    let spi = transport.spi(&opts.spi)?;
    let jedec_id = SpiFlash::read_jedec_id(&*spi, 16)?;
    log::info!("jedec_id = {:x?}", jedec_id);
    // Note: there is no specified bit pattern after the end of the JEDEC ID.
    // OpenTitan returns zeros.  Some devices return 0xFF or repeat the byte sequence.
    assert_eq!(
        jedec_id,
        [
            0x7f, 0x7f, 0x7f, // 3 continuation codes of 0x7F.
            0x56, // Manufacturer ID of 0x56.
            0x34, 0x12, // Device ID 0x1234 (in little endian order).
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0 // All zeros up to read length.
        ]
    );
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;
    uart.clear_rx_buffer()?;

    execute_test!(test_jedec_id, &opts, &transport);
    Ok(())
}
