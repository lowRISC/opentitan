// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use regex::Regex;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::spiflash::{BlockEraseSize, SpiFlash, SupportedAddressModes, WriteGranularity};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};
use opentitanlib::util::parse_int::ParseInt;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "5s",
        help = "Bootstrap detection timeout",
    )]
    timeout: Duration,

    #[structopt(
        long, parse(try_from_str=usize::from_str),
        default_value = "12",
        help = "JEDEC page of manufacturer",
    )]
    jedec_page: usize,

    #[structopt(
        long, parse(try_from_str=u8::from_str),
        default_value = "0xEF",
        help = "JEDEC ID of manufacturer",
    )]
    jedec_id: u8,

    #[structopt(
        long, parse(try_from_str=u8::from_str),
        default_value = "0x08",
        help = "JEDEC manufacturer product ID",
    )]
    jedec_product: u8,

    #[structopt(
        long, parse(try_from_str=u32::from_str),
        default_value = "0x100000",
        help = "Size of the internal flash",
    )]
    flash_size: u32,
}

#[derive(Debug, PartialEq, Eq)]
enum BootstrapRequest {
    No,
    Yes,
}

fn test_bootstrap_entry(
    opts: &Opts,
    transport: &TransportWrapper,
    request: BootstrapRequest,
) -> Result<()> {
    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("0")?;

    // Look for the bootstrap signal from the ROM.
    // When enabled, we expect the uart to emit a message indicating bootstrap entry.
    // When disabled, we expect the ROM to indicate boot failure.
    let (success, failure) = match request {
        BootstrapRequest::No => (Regex::new(r"BFV:")?, Regex::new(r"bootstrap:1\r\n")?),
        BootstrapRequest::Yes => (Regex::new(r"bootstrap:1\r\n")?, Regex::new(r"BFV:")?),
    };
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(success),
        exit_failure: Some(failure),
        ..Default::default()
    };

    match request {
        BootstrapRequest::No => transport.remove_pin_strapping("ROM_BOOTSTRAP")?,
        BootstrapRequest::Yes => transport.apply_pin_strapping("ROM_BOOTSTRAP")?,
    }
    let reset_delay = opts
        .init
        .bootstrap
        .options
        .reset_delay
        .unwrap_or(Duration::from_millis(50));
    transport.reset_target(reset_delay, true)?;

    // Now watch the console for the exit conditions.
    let mut stdout = std::io::stdout();
    let result = console.interact(&*uart, None, Some(&mut stdout))?;
    match result {
        ExitStatus::ExitSuccess => {}
        _ => {
            bail!("FAIL: {:?}", result);
        }
    };

    // Now check whether the SPI device is responding to status messages
    let spi = transport.spi("0")?;
    let status = SpiFlash::read_status(&*spi)?;
    match request {
        BootstrapRequest::No => assert_eq!(status, 0xff),
        BootstrapRequest::Yes => assert_eq!(status, 0x00),
    }
    Ok(())
}

fn test_jedec_id(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("0")?;
    let id = SpiFlash::read_jedec_id(&*spi, 16)?;
    log::info!("Read jedec id: {:x?}", id);
    let mut index = 0;
    while id[index] == 0x7f {
        index += 1;
    }
    let page = index;
    let manufacturer = id[index];
    let product = id[index + 1];
    let density = id[index + 2];

    assert_eq!(page, opts.jedec_page);
    assert_eq!(manufacturer, opts.jedec_id);
    assert_eq!(product, opts.jedec_product);
    assert_eq!(1u32 << density, opts.flash_size);
    Ok(())
}

fn test_write_enable_disable(transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("0")?;

    assert_eq!(SpiFlash::read_status(&*spi)?, 0x0);

    SpiFlash::set_write_enable(&*spi)?;
    assert_eq!(SpiFlash::read_status(&*spi)?, 0x2);

    SpiFlash::set_write_disable(&*spi)?;
    assert_eq!(SpiFlash::read_status(&*spi)?, 0x0);

    Ok(())
}

fn test_sfdp(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("0")?;
    let sfdp = SpiFlash::read_sfdp(&*spi)?;
    log::info!("SFDP: {:#x?}", sfdp);

    // We expect a SFDP header of version 1.10 with no additional phdrs
    // except the mandatory JDEC phdr.
    assert_eq!(sfdp.header.signature, 0x50444653);
    assert_eq!(sfdp.header.minor, 0xa);
    assert_eq!(sfdp.header.major, 0x1);
    assert_eq!(sfdp.header.nph, 0x0);
    assert_eq!(sfdp.header.reserved, 0xff);

    // Check the parameters of the mandatory phdr.
    assert_eq!(sfdp.phdr[0].id, 0x0);
    assert_eq!(sfdp.phdr[0].minor, 0x7);
    assert_eq!(sfdp.phdr[0].major, 0x1);
    assert_eq!(sfdp.phdr[0].dwords, 0x17);
    assert_eq!(sfdp.phdr[0].offset, 0x10);

    // Check the values of the JEDEC parameters.
    // TODO(lowRISC/opentitan#14457): Update these checks after updating the
    // SFDP parser in opentitanlib.
    assert_eq!(sfdp.jedec.block_erase_size, BlockEraseSize::Block4KiB);
    assert_eq!(
        sfdp.jedec.write_granularity,
        WriteGranularity::Granularity64Bytes
    );
    assert_eq!(sfdp.jedec.write_en_required, true);
    assert_eq!(sfdp.jedec.write_en_opcode, 0x50);
    assert_eq!(sfdp.jedec.erase_opcode_4kib, 0x20);
    assert_eq!(sfdp.jedec.support_fast_read_112, false);
    assert_eq!(sfdp.jedec.address_modes, SupportedAddressModes::Mode3b);
    assert_eq!(sfdp.jedec.support_double_rate_clocking, false);
    assert_eq!(sfdp.jedec.support_fast_read_122, false);
    assert_eq!(sfdp.jedec.support_fast_read_144, false);
    assert_eq!(sfdp.jedec.support_fast_read_114, false);
    assert_eq!(sfdp.jedec.support_fast_read_222, false);
    assert_eq!(sfdp.jedec.support_fast_read_444, false);
    assert_eq!(sfdp.jedec.density, opts.flash_size);
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(
        test_bootstrap_entry,
        &opts,
        &transport,
        BootstrapRequest::No
    );
    execute_test!(
        test_bootstrap_entry,
        &opts,
        &transport,
        BootstrapRequest::Yes
    );
    execute_test!(test_jedec_id, &opts, &transport);
    execute_test!(test_sfdp, &opts, &transport);
    execute_test!(test_write_enable_disable, &transport);
    Ok(())
}
