// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use object::{Object, ObjectSymbol};
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::i2c::{Bus, I2cError, Mode, Transfer};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::{MemWrite32Req, MemWriteReq};
use opentitanlib::test_utils::test_status::TestStatus;
use opentitanlib::uart::console::UartConsole;

const SMBUS_ARP_ADDR: u8 = 0x61;

const PEC_LUT: [u8; 256] = [
    0x00, 0x07, 0x0e, 0x09, 0x1c, 0x1b, 0x12, 0x15, 0x38, 0x3f, 0x36, 0x31, 0x24, 0x23, 0x2a, 0x2d,
    0x70, 0x77, 0x7e, 0x79, 0x6c, 0x6b, 0x62, 0x65, 0x48, 0x4f, 0x46, 0x41, 0x54, 0x53, 0x5a, 0x5d,
    0xe0, 0xe7, 0xee, 0xe9, 0xfc, 0xfb, 0xf2, 0xf5, 0xd8, 0xdf, 0xd6, 0xd1, 0xc4, 0xc3, 0xca, 0xcd,
    0x90, 0x97, 0x9e, 0x99, 0x8c, 0x8b, 0x82, 0x85, 0xa8, 0xaf, 0xa6, 0xa1, 0xb4, 0xb3, 0xba, 0xbd,
    0xc7, 0xc0, 0xc9, 0xce, 0xdb, 0xdc, 0xd5, 0xd2, 0xff, 0xf8, 0xf1, 0xf6, 0xe3, 0xe4, 0xed, 0xea,
    0xb7, 0xb0, 0xb9, 0xbe, 0xab, 0xac, 0xa5, 0xa2, 0x8f, 0x88, 0x81, 0x86, 0x93, 0x94, 0x9d, 0x9a,
    0x27, 0x20, 0x29, 0x2e, 0x3b, 0x3c, 0x35, 0x32, 0x1f, 0x18, 0x11, 0x16, 0x03, 0x04, 0x0d, 0x0a,
    0x57, 0x50, 0x59, 0x5e, 0x4b, 0x4c, 0x45, 0x42, 0x6f, 0x68, 0x61, 0x66, 0x73, 0x74, 0x7d, 0x7a,
    0x89, 0x8e, 0x87, 0x80, 0x95, 0x92, 0x9b, 0x9c, 0xb1, 0xb6, 0xbf, 0xb8, 0xad, 0xaa, 0xa3, 0xa4,
    0xf9, 0xfe, 0xf7, 0xf0, 0xe5, 0xe2, 0xeb, 0xec, 0xc1, 0xc6, 0xcf, 0xc8, 0xdd, 0xda, 0xd3, 0xd4,
    0x69, 0x6e, 0x67, 0x60, 0x75, 0x72, 0x7b, 0x7c, 0x51, 0x56, 0x5f, 0x58, 0x4d, 0x4a, 0x43, 0x44,
    0x19, 0x1e, 0x17, 0x10, 0x05, 0x02, 0x0b, 0x0c, 0x21, 0x26, 0x2f, 0x28, 0x3d, 0x3a, 0x33, 0x34,
    0x4e, 0x49, 0x40, 0x47, 0x52, 0x55, 0x5c, 0x5b, 0x76, 0x71, 0x78, 0x7f, 0x6a, 0x6d, 0x64, 0x63,
    0x3e, 0x39, 0x30, 0x37, 0x22, 0x25, 0x2c, 0x2b, 0x06, 0x01, 0x08, 0x0f, 0x1a, 0x1d, 0x14, 0x13,
    0xae, 0xa9, 0xa0, 0xa7, 0xb2, 0xb5, 0xbc, 0xbb, 0x96, 0x91, 0x98, 0x9f, 0x8a, 0x8d, 0x84, 0x83,
    0xde, 0xd9, 0xd0, 0xd7, 0xc2, 0xc5, 0xcc, 0xcb, 0xe6, 0xe1, 0xe8, 0xef, 0xfa, 0xfd, 0xf4, 0xf3,
];

#[repr(u8)]
enum SmbusArpCmd {
    PrepareToArp = 0x01,
    ResetDevice = 0x02,
    GetUdid = 0x03,
    AssignAddress = 0x04,
}

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Name of the debugger's I2C interface.
    #[arg(long, default_value = "0")]
    i2c: String,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

fn calc_pec(init: u8, next_bytes: &[u8]) -> u8 {
    let mut rem = init;
    for x in next_bytes.iter() {
        rem = PEC_LUT[(rem ^ x) as usize];
    }
    rem
}

fn prepare_to_arp(i2c: &Rc<dyn Bus>) -> Result<()> {
    let mut cmd_bytes = [SmbusArpCmd::PrepareToArp as u8, 0u8];
    cmd_bytes[1] = calc_pec(0, &cmd_bytes[0..1]);
    let cmd = Transfer::Write(&cmd_bytes);
    i2c.run_transaction(Some(SMBUS_ARP_ADDR), &mut [cmd])?;
    Ok(())
}

fn reset_device(i2c: &Rc<dyn Bus>) -> Result<()> {
    let mut cmd_bytes = [SmbusArpCmd::ResetDevice as u8, 0u8];
    cmd_bytes[1] = calc_pec(0, &cmd_bytes[0..1]);
    let cmd = Transfer::Write(&cmd_bytes);
    i2c.run_transaction(Some(SMBUS_ARP_ADDR), &mut [cmd])?;
    Ok(())
}

fn get_udid(i2c: &Rc<dyn Bus>, udid: &mut [u8; 16]) -> Result<()> {
    let cmd_bytes = [SmbusArpCmd::GetUdid as u8];
    let cmd = Transfer::Write(&cmd_bytes);
    let mut read_bytes = [0u8; 19];
    let read = Transfer::Read(&mut read_bytes);
    i2c.run_transaction(Some(SMBUS_ARP_ADDR), &mut [cmd, read])?;
    assert_eq!(read_bytes[0], 17);
    udid.copy_from_slice(&read_bytes[1..17]);
    // The device should have no address yet.
    assert_eq!(read_bytes[17], 0xff);
    let pec = calc_pec(0, &read_bytes[0..18]);
    assert_eq!(read_bytes[18], pec);
    Ok(())
}

fn assign_address(i2c: &Rc<dyn Bus>, udid: &[u8; 16], address: u8) -> Result<()> {
    let mut cmd_bytes = [0u8; 20];
    cmd_bytes[0] = SmbusArpCmd::AssignAddress as u8;
    cmd_bytes[1] = 17u8;
    cmd_bytes[2..18].copy_from_slice(udid);
    cmd_bytes[18] = (address << 1) | 1;
    cmd_bytes[19] = calc_pec(0, &cmd_bytes[0..19]);
    let cmd = Transfer::Write(&cmd_bytes);
    i2c.run_transaction(Some(SMBUS_ARP_ADDR), &mut [cmd])?;
    Ok(())
}

fn write_scratch(i2c: &Rc<dyn Bus>, i2c_addr: u8, cmd: u8, msg: &[u8; 32]) -> Result<()> {
    let mut cmd_bytes: Vec<u8> = Vec::new();
    cmd_bytes.push(cmd);
    cmd_bytes.extend_from_slice(msg);
    let cmd = Transfer::Write(cmd_bytes.as_slice());
    i2c.run_transaction(Some(i2c_addr), &mut [cmd])?;
    Ok(())
}

fn read_scratch(i2c: &Rc<dyn Bus>, i2c_addr: u8, cmd: u8, msg: &mut [u8; 32]) -> Result<()> {
    let cmd_bytes: [u8; 1] = [cmd];
    let write_cmd = Transfer::Write(&cmd_bytes);
    let read_cmd = Transfer::Read(msg);
    i2c.run_transaction(Some(i2c_addr), &mut [write_cmd, read_cmd])?;
    Ok(())
}

fn test_smbus_arp_sequence(
    opts: &Opts,
    transport: &TransportWrapper,
    udid_addr: u32,
    init_done_addr: u32,
    message_reg_addr: u32,
) -> Result<()> {
    let uart = transport.uart("console")?;
    let mut expected_udid = [0u8; 16];
    for (i, item) in expected_udid.iter_mut().enumerate() {
        *item = i as u8;
    }
    const MESSAGE_REG: u8 = 0xdu8;
    MemWriteReq::execute(&*uart, udid_addr, &expected_udid)?;
    MemWrite32Req::execute(&*uart, message_reg_addr, MESSAGE_REG.into())?;
    MemWrite32Req::execute(&*uart, init_done_addr, 1u32)?;

    let i2c = transport.i2c(&opts.i2c)?;
    i2c.set_mode(Mode::Host)?;
    UartConsole::wait_for(&*uart, &TestStatus::InWfi.wait_pattern(), opts.timeout)?;

    log::info!("Prepare to ARP");
    if let Err(x) = prepare_to_arp(&i2c) {
        // These parts are mostly to print out more console info on failures.
        let _ = UartConsole::wait_for(&*uart, r"FAIL[^\r\n]*", opts.timeout)?;
        return Err(x);
    }
    if let Err(x) = reset_device(&i2c) {
        let _ = UartConsole::wait_for(&*uart, r"FAIL[^\r\n]*", opts.timeout)?;
        return Err(x);
    }

    log::info!("Get UDID");
    let mut udid = [0u8; 16];
    if let Err(x) = get_udid(&i2c, &mut udid) {
        let _ = UartConsole::wait_for(&*uart, r"FAIL[^\r\n]*", opts.timeout)?;
        return Err(x);
    }
    assert_eq!(udid, expected_udid);

    log::info!("Assign address");
    assign_address(&i2c, &udid, 0x57u8)?;
    let _ = UartConsole::wait_for(&*uart, r"New i2c address assigned[^\r\n]*", opts.timeout)?;

    let msg_to_dut = [0xa5u8; 32];
    log::info!("Issue unsupported command");
    if write_scratch(&i2c, 0x57u8, !MESSAGE_REG, &msg_to_dut).is_err() {
        log::info!("Got an expected error");
    } else {
        return Err(
            I2cError::Generic("Expected NACK, but transaction accepted".to_string()).into(),
        );
    }
    log::info!("Write scratch");
    if let Err(x) = write_scratch(&i2c, 0x57u8, MESSAGE_REG, &msg_to_dut) {
        let _ = UartConsole::wait_for(&*uart, r"FAIL[^\r\n]*", opts.timeout)?;
        return Err(x);
    }
    log::info!("Read scratch");
    let mut msg_from_dut = [0u8; 32];
    if let Err(x) = read_scratch(&i2c, 0x57u8, MESSAGE_REG, &mut msg_from_dut) {
        let _ = UartConsole::wait_for(&*uart, r"FAIL[^\r\n]*", opts.timeout)?;
        return Err(x);
    }
    assert_eq!(msg_to_dut, msg_from_dut);
    let _ = UartConsole::wait_for(&*uart, r"PASS[^\r\n]*", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    /* Load the ELF binary and get the address of the `kPhase` variable
     * in example_sival.c */
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let elf_file = object::File::parse(&*elf_binary)?;
    let mut symbols = HashMap::<String, u32>::new();
    for sym in elf_file.symbols() {
        symbols.insert(sym.name()?.to_owned(), sym.address() as u32);
    }
    let udid_address = symbols
        .get("kSmbusUdid")
        .expect("Provided ELF missing 'kSmbusUdid' symbol");
    let init_done_address = symbols
        .get("kTestInitDone")
        .expect("Provided ELF missing 'kTestInitDone' symbol");
    let message_addr_address = symbols
        .get("kMessageAddr")
        .expect("Provided ELF missing 'kMessageAddr' symbol");

    let transport = opts.init.init_target()?;
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;
    uart.clear_rx_buffer()?;

    execute_test!(
        test_smbus_arp_sequence,
        &opts,
        &transport,
        *udid_address,
        *init_done_address,
        *message_addr_address,
    );
    Ok(())
}
