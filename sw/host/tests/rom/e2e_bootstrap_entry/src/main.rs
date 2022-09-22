// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use regex::Regex;
use std::matches;
use std::ops::Drop;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::spi::Transfer;
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
/// Calling `BootstrapTest::start()` resets the chip, erases its flash and puts it in bootstrap
/// mode (assuming it's enabled). Strapping pins are released, the chip is reset, and its flash is
/// erased when the returned struct is dropped, typically at the end of the test point.
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
        let spi = transport.spi("0").unwrap();
        SpiFlash::from_spi(&*spi)
            .unwrap()
            .chip_erase(&*spi)
            .unwrap();
        transport.reset_target(reset_delay, true).unwrap();
        Ok(b)
    }
}

impl<'a> Drop for BootstrapTest<'a> {
    fn drop(&mut self) {
        self.transport.apply_pin_strapping("ROM_BOOTSTRAP").unwrap();
        self.transport.reset_target(self.reset_delay, true).unwrap();
        let spi = self.transport.spi("0").unwrap();
        SpiFlash::from_spi(&*spi)
            .unwrap()
            .chip_erase(&*spi)
            .unwrap();
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
    let uart = transport.uart("console")?;
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
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
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
    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"BFV:")?),
        exit_failure: Some(Regex::new(r"bootstrap:1\r\n")?),
        ..Default::default()
    };

    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Now watch the console for the exit conditions.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
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

fn test_bootstrap_shutdown(
    opts: &Opts,
    transport: &TransportWrapper,
    cmd: u8,
    bfv: &str,
) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;

    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(Duration::new(2, 0)),
        // `kErrorBootPolicyBadIdentifier` (0142500d) is defined in `error.h`.
        exit_success: Some(Regex::new(
            format!("(?s)BFV:{bfv}\r\n.*BFV:0142500d\r\n").as_str(),
        )?),
        ..Default::default()
    };
    // Send CHIP_ERASE to transition to phase 2.
    SpiFlash::from_spi(&*spi)?.chip_erase(&*spi)?;
    // Remove strapping so that chip fails to boot instead of going into bootstrap.
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    // SECTOR_ERASE with invalid address to trigger a shutdown.
    SpiFlash::set_write_enable(&*spi)?;
    let bad_erase = [cmd, 0xff, 0xff, 0xff];
    spi.run_transaction(&mut [Transfer::Write(&bad_erase)])?;
    // We should see the expected BFVs.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }
    // Also verify that the chip is no longer in bootstrap mode.
    assert!(matches!(
        SpiFlash::read_sfdp(&*spi)
            .unwrap_err()
            .downcast::<sfdp::Error>()
            .unwrap(),
        sfdp::Error::WrongHeaderSignature(..)
    ));

    Ok(())
}

fn test_bootstrap_phase1_reset(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;

    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    // RESET should be ignored and we should not see any messages.
    let mut console = UartConsole {
        timeout: Some(Duration::new(1, 0)),
        exit_failure: Some(Regex::new(".+")?),
        ..Default::default()
    };
    // Discard buffered messages before interacting with the console.
    uart.clear_rx_buffer()?;
    SpiFlash::chip_reset(&*spi)?;
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::Timeout {
        bail!("FAIL: {:?}", result);
    }

    Ok(())
}

fn test_bootstrap_phase1_page_program(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;

    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(Duration::new(1, 0)),
        // `kErrorBootPolicyBadIdentifier` (0142500d) is defined in `error.h`.
        exit_success: Some(Regex::new("BFV:0142500d\r\n")?),
        // `kErrorBootPolicyBadLength` (0242500d) is defined in `error.h`.
        exit_failure: Some(Regex::new("BFV:0242500d\r\n")?),
        ..Default::default()
    };
    SpiFlash::from_spi(&*spi)?
        // Write "OTRE" to the identifier field of the manifest in the second slot.
        // Note: We must start at a flash-word-aligned address.
        .program(&*spi, 0x80330, &0x4552544f_00000000u64.to_le_bytes())?;
    // Remove strapping so that chip fails to boot instead of going into bootstrap.
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // We should see the expected BFV.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }

    Ok(())
}

fn test_bootstrap_phase1_erase(
    opts: &Opts,
    transport: &TransportWrapper,
    erase_cmd: u8,
) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;
    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    let spiflash = SpiFlash::from_spi(&*spi)?;
    let mut console = UartConsole {
        timeout: Some(Duration::new(1, 0)),
        ..Default::default()
    };

    let erase = || match erase_cmd {
        SpiFlash::SECTOR_ERASE => spiflash.erase(&*spi, 0, 4096),
        SpiFlash::CHIP_ERASE => spiflash.chip_erase(&*spi),
        _ => bail!("Unexpected erase command opcode: {:?}", erase_cmd),
    };

    // Send `erase_cmd` to transition to phase 2.
    erase()?
        // Write "OTRE" to the identifier field of the manifest in the second slot.
        .program(&*spi, 0x80330, &0x4552544f_00000000u64.to_le_bytes())?;

    // Remove strapping so that chip fails to boot instead of going into bootstrap.
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    // `kErrorBootPolicyBadLength` (0242500d) is defined in `error.h`.
    console.exit_success = Some(Regex::new("BFV:0242500d")?);
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }

    // Put the chip into bootstrap mode again and erase.
    transport.apply_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    erase()?;
    uart.clear_rx_buffer()?;
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    // `kErrorBootPolicyBadIdentifier` (0142500d) is defined in `error.h`.
    console.exit_success = Some(Regex::new("BFV:0142500d")?);
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }

    Ok(())
}

fn test_bootstrap_phase1_read(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;
    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(Duration::new(1, 0)),
        ..Default::default()
    };

    SpiFlash::from_spi(&*spi)?
        // Send CHIP_ERASE to transition to phase 2.
        .chip_erase(&*spi)?
        // Write "OTRE" to the identifier field of the manifest in the second slot.
        .program(&*spi, 0x80330, &0x4552544f_00000000u64.to_le_bytes())?;

    // Remove strapping so that chip fails to boot instead of going into bootstrap.
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    // `kErrorBootPolicyBadLength` (0242500d) is defined in `error.h`.
    console.exit_success = Some(Regex::new("0242500d")?);
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }

    transport.apply_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    assert_eq!(SpiFlash::read_status(&*spi)?, 0x00);
    let mut buf: [u8; 8] = [0xa5; 8];
    SpiFlash::from_spi(&*spi)?.read(&*spi, 0x80330, &mut buf)?;
    log::info!("Received: {:?}", &buf);
    assert_ne!(u64::from_le_bytes(buf), 0x4552544f_00000000u64);

    Ok(())
}

fn test_bootstrap_phase2_reset(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;

    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(Duration::new(1, 0)),
        // `kErrorBootPolicyBadIdentifier` (0142500d) is defined in `error.h`.
        exit_success: Some(Regex::new("BFV:0142500d\r\n")?),
        ..Default::default()
    };
    // Send CHIP_ERASE to transition to phase 2.
    SpiFlash::from_spi(&*spi)?.chip_erase(&*spi)?;
    // Remove strapping so that chip fails to boot instead of going into bootstrap.
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    // Discard buffered messages before interacting with the console.
    uart.clear_rx_buffer()?;
    SpiFlash::chip_reset(&*spi)?;
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }

    assert!(matches!(
        SpiFlash::read_sfdp(&*spi)
            .unwrap_err()
            .downcast::<sfdp::Error>()
            .unwrap(),
        sfdp::Error::WrongHeaderSignature(..)
    ));

    Ok(())
}

fn test_bootstrap_phase2_page_program(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;
    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    SpiFlash::from_spi(&*spi)?
        // Send CHIP_ERASE to transition to phase 2.
        .chip_erase(&*spi)?
        // Write "OTRE" to the identifier field of the manifest in the second slot.
        .program(&*spi, 0x80330, &0x4552544f_00000000u64.to_le_bytes())?;

    let mut console = UartConsole {
        timeout: Some(Duration::new(1, 0)),
        // `kErrorBootPolicyBadLength` (0242500d) is defined in `error.h`.
        exit_success: Some(Regex::new("BFV:0242500d\r\n")?),
        ..Default::default()
    };
    // Remove strapping so that chip fails to boot instead of going into bootstrap.
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }

    Ok(())
}

fn test_bootstrap_phase2_erase(
    opts: &Opts,
    transport: &TransportWrapper,
    erase_cmd: u8,
) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;
    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    let spiflash = SpiFlash::from_spi(&*spi)?;
    let erase = || match erase_cmd {
        // We should erase the page of the identifier of the second slot.
        SpiFlash::SECTOR_ERASE => spiflash.erase(&*spi, 0x80330 & (!4096 + 1), 4096),
        SpiFlash::CHIP_ERASE => spiflash.chip_erase(&*spi),
        _ => bail!("Unexpected erase command opcode: {:?}", erase_cmd),
    };

    // Send `erase_cmd` to transition to phase 2.
    erase()?
        // Write "OTRE" to the identifier field of the manifest in the second slot.
        .program(&*spi, 0x80330, &0x4552544f_00000000u64.to_le_bytes())?;
    // Erase again.
    erase()?;

    let mut console = UartConsole {
        timeout: Some(Duration::new(1, 0)),
        // `kErrorBootPolicyBadIdentifier` (0142500d) is defined in `error.h`.
        exit_success: Some(Regex::new("BFV:0142500d\r\n")?),
        ..Default::default()
    };
    // Remove strapping so that chip fails to boot instead of going into bootstrap.
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }

    Ok(())
}

fn test_bootstrap_phase2_read(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let _bs = BootstrapTest::start(transport, opts.init.bootstrap.options.reset_delay)?;
    let spi = transport.spi("0")?;
    let uart = transport.uart("console")?;
    let mut read_buf = [0u8; 8];

    SpiFlash::from_spi(&*spi)?
        // Send CHIP_ERASE to transition to phase 2.
        .chip_erase(&*spi)?
        // Write "OTRE" to the identifier field of the manifest in the second slot.
        .program(&*spi, 0x80330, &0x4552544f_00000000u64.to_le_bytes())?
        // Read 8 bytes starting from 0x80330.
        .read(&*spi, 0x80330, &mut read_buf)?;
    let received = u64::from_le_bytes(read_buf);
    log::info!("Received: {:#x}", received);
    assert_ne!(received, 0x4552544f_00000000u64);

    let mut console = UartConsole {
        timeout: Some(Duration::new(1, 0)),
        // `kErrorBootPolicyBadLength` (0242500d) is defined in `error.h`.
        exit_success: Some(Regex::new("BFV:0242500d\r\n")?),
        ..Default::default()
    };
    // Remove strapping so that chip fails to boot instead of going into bootstrap.
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    }

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
    for (cmd, bfv) in [
        // `kErrorBootstrapEraseAddress` (01425303) is defined in `error.h`.
        (SpiFlash::SECTOR_ERASE, "01425303"),
        // `kErrorBootstrapProgramAddress` (02425303) is defined in `error.h`.
        (SpiFlash::PAGE_PROGRAM, "02425303"),
    ] {
        execute_test!(test_bootstrap_shutdown, &opts, &transport, cmd, bfv);
    }
    execute_test!(test_bootstrap_phase1_reset, &opts, &transport);
    execute_test!(test_bootstrap_phase1_page_program, &opts, &transport);
    for erase_cmd in [SpiFlash::SECTOR_ERASE, SpiFlash::CHIP_ERASE] {
        execute_test!(test_bootstrap_phase1_erase, &opts, &transport, erase_cmd);
    }
    execute_test!(test_bootstrap_phase1_read, &opts, &transport);
    execute_test!(test_bootstrap_phase2_reset, &opts, &transport);
    execute_test!(test_bootstrap_phase2_page_program, &opts, &transport);
    for erase_cmd in [SpiFlash::SECTOR_ERASE, SpiFlash::CHIP_ERASE] {
        execute_test!(test_bootstrap_phase2_erase, &opts, &transport, erase_cmd);
    }
    execute_test!(test_bootstrap_phase2_read, &opts, &transport);

    Ok(())
}
