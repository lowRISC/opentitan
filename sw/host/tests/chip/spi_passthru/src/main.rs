// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::eeprom::AddressMode;
use opentitanlib::io::spi::{Target, Transfer};
use opentitanlib::spiflash::sfdp::SectorErase;
use opentitanlib::spiflash::{EraseMode, ReadMode, Sfdp, SpiFlash};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::spi_passthru::{
    ConfigJedecId, SfdpData, SpiFlashEraseSector, SpiFlashReadSfdp, SpiFlashWrite, SpiMailboxMap,
    SpiMailboxWrite, SpiPassthruSwapMap, StatusRegister, UploadInfo,
};
use opentitanlib::transport::Capability;
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
            offset as u8,
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

fn test_sector_erase(
    opts: &Opts,
    transport: &TransportWrapper,
    address: u32,
    size: u32,
    force_4b: bool,
) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    let mut flash = SpiFlash {
        // Double the flash size so we can test 3b and 4b addresses.
        size: 32 * 1024 * 1024,
        // Use block erase mode, causing SpiFlah::erase to select the best type
        // of erase opcode based on address alignment and size.
        erase_mode: EraseMode::Block,
        // Since we aren't creating SpiFlash from an SFDP table, fill in the
        // erase information with typical SFDP-supplied values.
        erase: vec![
            SectorErase {
                size: 65536,
                opcode: if force_4b {
                    SpiFlash::BLOCK_ERASE_64K_4B
                } else {
                    SpiFlash::BLOCK_ERASE_64K
                },
                time: None,
            },
            SectorErase {
                size: 32768,
                opcode: if force_4b {
                    SpiFlash::BLOCK_ERASE_32K_4B
                } else {
                    SpiFlash::BLOCK_ERASE_64K
                },
                time: None,
            },
            SectorErase {
                size: 4096,
                opcode: if force_4b {
                    SpiFlash::SECTOR_ERASE_4B
                } else {
                    SpiFlash::BLOCK_ERASE_64K
                },
                time: None,
            },
        ],
        ..Default::default()
    };

    let expected_opcode = flash
        .erase
        .iter()
        .find(|e| e.size == size)
        .expect("erase size")
        .opcode;

    // Make sure we're in a mode appropriate for the address.
    let mode = if force_4b || address >= 0x1000000 {
        AddressMode::Mode4b
    } else {
        AddressMode::Mode3b
    };
    flash.set_address_mode(&*spi, mode)?;
    let info = UploadInfo::execute(&*uart, || {
        flash.erase(&*spi, address, size)?;
        Ok(())
    })?;

    assert_eq!(info.opcode, expected_opcode);
    assert_eq!(info.has_address, true);
    assert_eq!(info.addr_4b, mode == AddressMode::Mode4b);
    assert_eq!(info.address, address);
    assert_eq!(info.data_len, 0);
    assert_eq!(
        info.flash_status & FLASH_STATUS_STD_BITS,
        FLASH_STATUS_WEL | FLASH_STATUS_WIP
    );
    Ok(())
}

fn test_page_program(opts: &Opts, transport: &TransportWrapper, address: u32) -> Result<()> {
    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;
    let data = (0..256).map(|x| x as u8).collect::<Vec<u8>>();
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
    let info = UploadInfo::execute(&*uart, || {
        flash.program(&*spi, address, &data)?;
        Ok(())
    })?;

    assert_eq!(info.opcode, SpiFlash::PAGE_PROGRAM);
    assert_eq!(info.has_address, true);
    assert_eq!(info.addr_4b, mode == AddressMode::Mode4b);
    assert_eq!(info.address, address);
    assert_eq!(info.data_len as usize, data.len());
    assert_eq!(info.data.as_slice(), data.as_slice());
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

fn test_read_flash(opts: &Opts, transport: &TransportWrapper, mode: ReadMode) -> Result<()> {
    log::info!("using read mode {:?}", mode);
    let capability = match mode {
        ReadMode::Standard => Ok(()),
        ReadMode::Fast => Ok(()),
        ReadMode::Dual => transport.capabilities()?.request(Capability::SPI_DUAL).ok(),
        ReadMode::Quad => transport.capabilities()?.request(Capability::SPI_QUAD).ok(),
    };
    if capability.is_err() {
        log::warn!(
            "Needed capability for {:?} not available.  Skipping test!",
            mode
        );
        return Ok(());
    }

    let uart = transport.uart("console")?;
    let spi = transport.spi(&opts.spi)?;

    let sfdp_read = SpiFlashReadSfdp {
        address: 0u32,
        length: 256u16,
    };
    let sfdp_data = sfdp_read.execute(&*uart)?;
    let sfdp = Sfdp::try_from(sfdp_data.data.as_slice())?;
    let spi_flash = {
        let mut flash = SpiFlash::from_sfdp(sfdp);
        flash.read_mode = mode;
        flash
    };

    // Put increasing count at 0x1000.
    let address_inc = 0x1000u32;
    let erase_op = SpiFlashEraseSector {
        address: address_inc,
        addr4b: false,
    };
    erase_op.execute(&*uart)?;

    let write_op_inc = SpiFlashWrite {
        address: address_inc,
        addr4b: false,
        data: (0..256).map(|x| x as u8).collect(),
        length: 256,
    };
    write_op_inc.execute(&*uart)?;

    // Put decreasing count at 0x11000.
    let address_dec = 0x11000u32;
    let erase_op = SpiFlashEraseSector {
        address: address_dec,
        addr4b: false,
    };
    erase_op.execute(&*uart)?;

    let write_op_dec = SpiFlashWrite {
        address: address_dec,
        addr4b: false,
        data: (0..256).map(|x| 255u8 - (x as u8)).collect(),
        length: 256,
    };
    write_op_dec.execute(&*uart)?;

    // Put count of evens in mailbox
    let write_op_mbox = SpiMailboxWrite {
        offset: 0u16,
        data: (0..256).map(|x| (x << 1) as u8).collect(),
        length: 256,
    };
    write_op_mbox.execute(&*uart)?;

    // Read from flash with no special mapping.
    let mut read_data = vec![0; 256];
    spi_flash.read(&*spi, address_inc, &mut read_data)?;
    assert_eq!(read_data.as_slice(), write_op_inc.data.as_slice());

    let mut read_data = vec![0; 256];
    spi_flash.read(&*spi, address_dec, &mut read_data)?;
    assert_eq!(read_data.as_slice(), write_op_dec.data.as_slice());

    // Turn on address translation, making address_dec point to address_inc.
    let address_swap = SpiPassthruSwapMap {
        mask: 0x10000u32,
        value: 0x00000u32,
    };
    address_swap.apply_address_swap(&*uart)?;

    let mut read_data = vec![0; 256];
    spi_flash.read(&*spi, address_dec, &mut read_data)?;
    assert_eq!(read_data.as_slice(), write_op_inc.data.as_slice());
    assert_ne!(read_data.as_slice(), write_op_dec.data.as_slice());

    // Turn address translation back off.
    let address_swap = SpiPassthruSwapMap {
        mask: 0u32,
        value: 0u32,
    };
    address_swap.apply_address_swap(&*uart)?;

    // Enable the mailbox at the increasing count's address, and check the read.
    let mbox_map = SpiMailboxMap {
        address: address_inc,
    };
    mbox_map.apply(&*uart)?;
    let mut read_data = vec![0; 256];
    spi_flash.read(&*spi, address_inc, &mut read_data)?;
    assert_eq!(read_data.as_slice(), write_op_mbox.data.as_slice());
    assert_ne!(read_data.as_slice(), write_op_inc.data.as_slice());

    // Disable the mailbox.
    SpiMailboxMap::disable(&*uart)?;
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

    execute_test!(test_read_flash, &opts, &transport, ReadMode::Standard);
    execute_test!(test_read_flash, &opts, &transport, ReadMode::Fast);
    execute_test!(test_read_flash, &opts, &transport, ReadMode::Dual);
    execute_test!(test_read_flash, &opts, &transport, ReadMode::Quad);
    execute_test!(test_jedec_id, &opts, &transport);
    execute_test!(test_enter_exit_4b_mode, &opts, &transport);
    execute_test!(test_write_enable_disable, &opts, &transport);
    execute_test!(test_read_status_extended, &opts, &transport);
    execute_test!(test_read_sfdp, &opts, &transport);
    execute_test!(test_chip_erase, &opts, &transport);
    // Test each of the erase opcodes based on the erase size.
    // Automatically switch into 4B mode based on the address.
    execute_test!(
        test_sector_erase,
        &opts,
        &transport,
        0x0000_4000,
        4096,
        false
    );
    execute_test!(
        test_sector_erase,
        &opts,
        &transport,
        0x0100_4000,
        4096,
        false
    );
    execute_test!(
        test_sector_erase,
        &opts,
        &transport,
        0x0001_0000,
        65536,
        false
    );
    execute_test!(
        test_sector_erase,
        &opts,
        &transport,
        0x0100_8000,
        32768,
        false
    );
    // Test each of the ERASE_*_4B opcodes.
    execute_test!(
        test_sector_erase,
        &opts,
        &transport,
        0x0000_4000,
        4096,
        true
    );
    execute_test!(
        test_sector_erase,
        &opts,
        &transport,
        0x0001_0000,
        65536,
        true
    );
    execute_test!(
        test_sector_erase,
        &opts,
        &transport,
        0x0100_8000,
        32768,
        true
    );
    execute_test!(test_page_program, &opts, &transport, 0x0000_4000);
    execute_test!(test_page_program, &opts, &transport, 0x0100_4000);
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
