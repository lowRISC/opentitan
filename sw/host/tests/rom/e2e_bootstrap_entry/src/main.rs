// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use regex::Regex;
use std::matches;
use std::ops::Drop;
use std::thread;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::spiflash::{
    sfdp, BlockEraseSize, SpiFlash, SupportedAddressModes, WriteGranularity,
};
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

/// A struct for isolating individual test points.
///
/// This is basically an example of the RAII technique.
/// Calling `BootstrapTest::start()` resets the chip and puts it in bootstrap mode (assuming it's
/// enabled). Strapping pins are released and the chip is reset when the returned struct is
/// dropped, typically at the end of the test point.
struct BootstrapTest<'a> {
    transport: &'a TransportWrapper,
    reset_delay: Duration,
}

impl<'a> BootstrapTest<'a> {
    pub fn start(transport: &'a TransportWrapper, reset_delay: Duration) -> Result<Self> {
        let b = BootstrapTest {
            transport,
            reset_delay,
        };
        transport.apply_pin_strapping("ROM_BOOTSTRAP")?;
        transport.reset_target(b.reset_delay, true)?;

        let spi = transport.spi("0")?;
        while SpiFlash::read_status(&*spi)? != 0 {
            thread::sleep(Duration::from_millis(10));
        }

        Ok(b)
    }
}

impl<'a> Drop for BootstrapTest<'a> {
    fn drop(&mut self) {
        self.transport
            .remove_pin_strapping("ROM_BOOTSTRAP")
            .unwrap();
        self.transport.reset_target(self.reset_delay, true).unwrap();
    }
}

fn test_bootstrap_enabled_requested(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;

    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("0")?;
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"bootstrap:1\r\n")?),
        exit_failure: Some(Regex::new(r"BFV:")?),
        ..Default::default()
    };

    transport.apply_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Now watch the console for the exit conditions.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    match result {
        ExitStatus::ExitSuccess => {}
        _ => {
            bail!("FAIL: {:?}", result);
        }
    };
    // Now check whether the SPI device is responding to status messages
    let spi = transport.spi("0")?;
    assert_eq!(SpiFlash::read_status(&*spi)?, 0x00);

    Ok(())
}

fn test_bootstrap_enabled_not_requested(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("0")?;
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"BFV:")?),
        exit_failure: Some(Regex::new(r"bootstrap:1\r\n")?),
        ..Default::default()
    };

    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Now watch the console for the exit conditions.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    match result {
        ExitStatus::ExitSuccess => {}
        _ => {
            bail!("FAIL: {:?}", result);
        }
    };

    // Now check whether the SPI device is responding to commands.
    // Note: CIPO line is in high-z state when CMD_INFO registers are not configured.
    // Use READ_SFDP instead of READ_STATUS to avoid false negatives when bootstrap is not
    // requested
    let spi = transport.spi("0")?;
    assert!(matches!(
        SpiFlash::read_sfdp(&*spi)
            .unwrap_err()
            .downcast::<sfdp::Error>()
            .unwrap(),
        sfdp::Error::WrongHeaderSignature(..)
    ));
    Ok(())
}

fn test_jedec_id(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;

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

fn test_write_enable_disable(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;

    let spi = transport.spi("0")?;

    assert_eq!(SpiFlash::read_status(&*spi)?, 0x0);

    SpiFlash::set_write_enable(&*spi)?;
    assert_eq!(SpiFlash::read_status(&*spi)?, 0x2);

    SpiFlash::set_write_disable(&*spi)?;
    assert_eq!(SpiFlash::read_status(&*spi)?, 0x0);

    Ok(())
}

fn test_sfdp(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;

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
    execute_test!(test_bootstrap_enabled_not_requested, &opts, &transport);
    execute_test!(test_bootstrap_enabled_requested, &opts, &transport);
    execute_test!(test_jedec_id, &opts, &transport);
    execute_test!(test_sfdp, &opts, &transport);
    execute_test!(test_write_enable_disable, &opts, &transport);
    Ok(())
}
