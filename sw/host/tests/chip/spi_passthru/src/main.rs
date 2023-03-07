// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::spi::{Target, Transfer};
use opentitanlib::spiflash::SpiFlash;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::spi_passthru::{ConfigJedecId, SfdpData, StatusRegister, UploadInfo};
use opentitanlib::uart::console::UartConsole;

const FLASH_STATUS_WIP: u32 = 0x01;
const FLASH_STATUS_WEL: u32 = 0x02;
const FLASH_STATUS_STD_BITS: u32 = FLASH_STATUS_WEL | FLASH_STATUS_WIP;

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

fn test_enter_exit_4b_mode(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    log::info!("Entering 4B address mode");
    spi.run_transaction(&mut [Transfer::Write(&[SpiFlash::ENTER_4B])])?;
    let sr = StatusRegister::read(&*uart)?;
    assert!(sr.addr_4b, "expected to be in 4b mode");

    log::info!("Exiting 4B address mode");
    spi.run_transaction(&mut [Transfer::Write(&[SpiFlash::EXIT_4B])])?;
    let sr = StatusRegister::read(&*uart)?;
    assert!(!sr.addr_4b, "expected to be in 3b mode");
    Ok(())
}

fn test_write_enable_disable(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    log::info!("Sending WRITE_ENABLE");
    spi.run_transaction(&mut [Transfer::Write(&[SpiFlash::WRITE_ENABLE])])?;
    let status = SpiFlash::read_status(&*spi)?;
    let sr = StatusRegister::read(&*uart)?;
    assert!(
        status as u32 & FLASH_STATUS_WEL != 0,
        "expected WEL set via read_status"
    );
    assert!(
        sr.status & FLASH_STATUS_WEL != 0,
        "expected WEL set on the device"
    );

    log::info!("Sending WRITE_DISABLE");
    spi.run_transaction(&mut [Transfer::Write(&[SpiFlash::WRITE_DISABLE])])?;
    let status = SpiFlash::read_status(&*spi)?;
    let sr = StatusRegister::read(&*uart)?;
    assert!(
        status as u32 & FLASH_STATUS_WEL == 0,
        "expected WEL clear via read_status"
    );
    assert!(
        sr.status & FLASH_STATUS_WEL == 0,
        "expected WEL clear on the device"
    );
    Ok(())
}

fn test_read_status_extended(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    let sr = StatusRegister {
        status: 0x5A55AA,
        addr_4b: false,
    };
    sr.write(&*uart)?;
    // Note: because we're programming the flash_status register in firmware,
    // we require one CS low-to-high transition to latch the values from the
    // CSR into the spi device.  We'd normally expect this type of register
    // setup to be done at init time and that the first SPI transaction will
    // be a READ_ID or READ_SFDP, thus latching the flash_status contents.
    //
    // In this test program, we simply issue a NOP transaction to the device.
    spi.run_transaction(&mut [Transfer::Write(&[SpiFlash::NOP])])?;
    let value = SpiFlash::read_status_ex(&*spi, None)?;
    assert_eq!(value, sr.status);
    Ok(())
}

fn read_sfdp(spi: &dyn Target, offset: u32) -> Result<Vec<u8>> {
    let mut buf = vec![0u8; 256];
    spi.run_transaction(&mut [
        // READ_SFDP always takes a 3-byte address followed by a dummy
        // byte regardless of address mode.
        Transfer::Write(&[
            SpiFlash::READ_SFDP,
            (offset >> 16) as u8,
            (offset >> 8) as u8,
            (offset >> 0) as u8,
            0, // Dummy byte.
        ]),
        Transfer::Read(&mut buf),
    ])?;
    Ok(buf)
}

fn test_read_sfdp(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    let sfdp = SfdpData {
        data: (0..256).map(|x| x as u8).collect(),
    };
    sfdp.write(&*uart)?;

    // Read and compare the whole SFDP buffer.
    let buf = read_sfdp(&*spi, 0)?;
    assert_eq!(buf, sfdp.data.as_slice());

    // Test a read that would go beyond the length of the SFDP data.
    // The observed behavior should be that the buffer recieved from
    // the device should wrap around.
    let buf = read_sfdp(&*spi, 0x30)?;
    let data = sfdp.data.as_slice();
    assert_eq!(buf[0x00..0xd0], data[0x30..0x100]);
    assert_eq!(buf[0xd0..0x100], data[0x00..0x30]);

    Ok(())
}

fn test_chip_erase(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    let flash = SpiFlash::default();

    let info = UploadInfo::execute(&*uart, || {
        flash.chip_erase(&*spi)?;
        Ok(())
    })?;

    assert_eq!(info.opcode, SpiFlash::CHIP_ERASE);
    assert_eq!(info.has_address, false);
    assert_eq!(info.data_len, 0);
    assert_eq!(
        info.flash_status & FLASH_STATUS_STD_BITS,
        FLASH_STATUS_WEL | FLASH_STATUS_WIP
    );
    Ok(())
}

fn test_write_status(opts: &Opts, transport: &TransportWrapper, opcode: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    let info = UploadInfo::execute(&*uart, || {
        spi.run_transaction(&mut [Transfer::Write(&[opcode])])?;
        Ok(())
    })?;

    assert_eq!(info.opcode, opcode);
    assert_eq!(info.has_address, false);
    assert_eq!(info.data_len, 0);
    assert_eq!(info.flash_status & FLASH_STATUS_STD_BITS, FLASH_STATUS_WIP);
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
    execute_test!(test_enter_exit_4b_mode, &opts, &transport);
    execute_test!(test_write_enable_disable, &opts, &transport);
    execute_test!(test_read_status_extended, &opts, &transport);
    execute_test!(test_read_sfdp, &opts, &transport);
    execute_test!(test_chip_erase, &opts, &transport);
    execute_test!(test_write_status, &opts, &transport, SpiFlash::WRITE_STATUS);
    execute_test!(
        test_write_status,
        &opts,
        &transport,
        SpiFlash::WRITE_STATUS2
    );
    execute_test!(
        test_write_status,
        &opts,
        &transport,
        SpiFlash::WRITE_STATUS3
    );
    Ok(())
}
