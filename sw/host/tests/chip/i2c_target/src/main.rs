// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::i2c::Transfer;
use opentitanlib::test_utils::e2e_command::TestCommand;
use opentitanlib::test_utils::i2c_target::{I2cTargetAddress, I2cTransaction};
use opentitanlib::test_utils::init::InitializeTest;
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
        default_value = "0",
        help = "Name of the debugger's I2C interface"
    )]
    i2c: String,
}

// A data pattern to send across the I2C bus:
// From: http://www.abrahamlincolnonline.org/lincoln/speeches/gettysburg.htm
const GETTYSBURG: &str = r#"Four score and seven years ago our fathers brought forth on this
continent, a new nation, conceived in Liberty, and dedicated to the
proposition that all men are created equal."#;

fn test_set_target_address(_opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    //let i2c = transport.i2c(&opts.i2c)?;
    let address = I2cTargetAddress {
        // Respond to address 0x33.
        id0: 0x33,
        mask0: 0x7f,
        // Respond to addressess 0x70-0x73.
        id1: 0x70,
        mask1: 0x7c,
    };
    address.write(&*uart)?;
    Ok(())
}

fn test_read_transaction(opts: &Opts, transport: &TransportWrapper, address: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    let i2c = transport.i2c(&opts.i2c)?;

    log::info!("Testing read transaction at I2C address {address:02x}");
    let txn = I2cTransaction::new(b"Hello");
    let mut result = vec![0u8; txn.length as usize];
    let rx_result = txn.execute_read(&*uart, || {
        i2c.run_transaction(address, &mut [Transfer::Read(&mut result)])
    })?;
    assert_eq!(result.as_slice(), txn.data.as_slice());
    assert_eq!(rx_result.address, address);
    assert_eq!(rx_result.continuation, 0);
    Ok(())
}

fn test_write_transaction(opts: &Opts, transport: &TransportWrapper, address: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    let i2c = transport.i2c(&opts.i2c)?;
    log::info!("Testing write transaction at I2C address {address:02x}");
    let result = I2cTransaction::execute_write(&*uart, TestCommand::I2cWriteTransaction, || {
        i2c.run_transaction(address, &mut [Transfer::Write(b"Hello World")])
    })?;
    let len = result.length as usize;
    assert_eq!(&result.data[0..len], b"Hello World");
    assert_eq!(result.address, address);
    assert_eq!(result.continuation, 0);
    Ok(())
}

fn test_write_transaction_slow(
    opts: &Opts,
    transport: &TransportWrapper,
    address: u8,
) -> Result<()> {
    let uart = transport.uart("console")?;
    let i2c = transport.i2c(&opts.i2c)?;
    log::info!("Testing slow write transaction at I2C address {address:02x}");
    let result =
        I2cTransaction::execute_write(&*uart, TestCommand::I2cWriteTransactionSlow, || {
            i2c.run_transaction(address, &mut [Transfer::Write(GETTYSBURG.as_bytes())])
        })?;
    let len = result.length as usize;
    assert_eq!(&result.data[0..len], GETTYSBURG.as_bytes());
    assert_eq!(result.address, address);
    assert_eq!(result.continuation, 0);
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

    execute_test!(test_set_target_address, &opts, &transport);
    execute_test!(test_read_transaction, &opts, &transport, 0x33);
    execute_test!(test_read_transaction, &opts, &transport, 0x70);
    execute_test!(test_read_transaction, &opts, &transport, 0x71);
    execute_test!(test_read_transaction, &opts, &transport, 0x72);
    execute_test!(test_read_transaction, &opts, &transport, 0x73);
    execute_test!(test_write_transaction, &opts, &transport, 0x33);
    execute_test!(test_write_transaction_slow, &opts, &transport, 0x33);
    Ok(())
}
