// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::BitbangEntry;
use opentitanlib::io::gpio::GpioPin;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::i2c::Transfer;
use opentitanlib::test_utils;
use opentitanlib::test_utils::e2e_command::TestCommand;
use opentitanlib::test_utils::i2c_target::{I2cTargetAddress, I2cTestConfig, I2cTransferStart};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::test_utils::status::Status;
use opentitanlib::uart::console::UartConsole;
use std::borrow::Borrow;
use std::rc::Rc;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Name of the debugger's I2C interface.
    #[arg(long, default_value = "TPM")]
    i2c: String,
}

// A data pattern to send across the I2C bus:
// From: http://www.abrahamlincolnonline.org/lincoln/speeches/gettysburg.htm
const GETTYSBURG: &str = r#"Four score and seven years ago our fathers brought forth on this
continent, a new nation, conceived in Liberty, and dedicated to the
proposition that all men are created equal."#;

fn test_set_target_address(_opts: &Opts, transport: &TransportWrapper, instance: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    let address = I2cTargetAddress {
        instance,
        // Respond to address 0x33.
        id0: 0x33,
        mask0: 0x7f,
        // Respond to addresses 0x70-0x73.
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
    let txn = I2cTransferStart::new(address, b"Hello", true);
    let mut result = vec![0u8; txn.length as usize];
    txn.execute_read(&*uart, || {
        i2c.run_transaction(Some(address), &mut [Transfer::Read(&mut result)])
    })?;
    assert_eq!(result.as_slice(), txn.data.as_slice());
    Ok(())
}

fn test_clock_stretching(opts: &Opts, transport: &TransportWrapper, address: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    let i2c = transport.i2c(&opts.i2c)?;

    let stretching_delay = I2cTestConfig {
        clock_stretching_delay_millis: 10,
    };
    stretching_delay.write(&*uart)?;

    log::info!("Testing read transaction with clock stretching at I2C address {address:02x}");
    let txn = I2cTransferStart::new(address, b"Stretching the clock", true);
    let mut result = vec![0u8; txn.length as usize];
    txn.execute_read(&*uart, || {
        i2c.run_transaction(Some(address), &mut [Transfer::Read(&mut result)])
    })?;

    let stretching_delay = I2cTestConfig {
        clock_stretching_delay_millis: 0,
    };
    stretching_delay.write(&*uart)?;

    assert_eq!(result.as_slice(), txn.data.as_slice());
    Ok(())
}

fn test_write_transaction(opts: &Opts, transport: &TransportWrapper, address: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    let i2c = transport.i2c(&opts.i2c)?;
    log::info!("Testing write transaction at I2C address {address:02x}");

    let transfer = I2cTransferStart::execute_write(&*uart, || {
        i2c.run_transaction(Some(address), &mut [Transfer::Write(b"Hello World")])
    })?;
    let len = transfer.length as usize;
    assert_eq!(&transfer.data[0..len], b"Hello World");
    assert_eq!(transfer.address, address);
    assert!(transfer.stop);
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
    let result = I2cTransferStart::execute_write_slow(&*uart, || {
        i2c.run_transaction(Some(address), &mut [Transfer::Write(GETTYSBURG.as_bytes())])
    })?;
    let len = result.length as usize;
    assert_eq!(&result.data[0..len], GETTYSBURG.as_bytes());
    assert_eq!(result.address, address);
    assert!(result.stop);
    Ok(())
}

fn test_wakeup_normal_sleep(opts: &Opts, transport: &TransportWrapper, address: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    let i2c = transport.i2c(&opts.i2c)?;
    TestCommand::EnterNormalSleep.send_with_crc(&*uart)?;
    std::thread::sleep(Duration::from_secs(2));
    let mut buf = [0u8; 8];
    log::info!("Issuing read transaction to sleeping chip. Expecting transaction error.");
    let result = i2c.run_transaction(Some(address), &mut [Transfer::Read(&mut buf)]);
    log::info!("Transaction error: {}", result.is_err());
    Status::recv(&*uart, Duration::from_secs(5), false)?;
    log::info!("Chip is awake.  Reissuing read transaction.");
    test_read_transaction(opts, transport, address)
}

fn test_wakeup_deep_sleep(
    opts: &Opts,
    transport: &TransportWrapper,
    address: u8,
    instance: u8,
) -> Result<()> {
    let uart = transport.uart("console")?;
    let i2c = transport.i2c(&opts.i2c)?;
    TestCommand::EnterDeepSleep.send_with_crc(&*uart)?;
    std::thread::sleep(Duration::from_secs(2));
    let mut buf = [0u8; 8];
    log::info!("Issuing read transaction to sleeping chip. Expecting transaction error.");
    let result = i2c.run_transaction(Some(address), &mut [Transfer::Read(&mut buf)]);
    log::info!("Transaction error: {}", result.is_err());
    Status::recv(&*uart, Duration::from_secs(5), false)?;
    log::info!("Chip is awake.  Reissuing read transaction.");
    test_set_target_address(opts, transport, instance)?;
    test_read_transaction(opts, transport, address)
}

fn test_write_repeated_start(
    _opts: &Opts,
    transport: &TransportWrapper,
    address: u8,
    gpio_pins: &[Rc<dyn GpioPin>],
) -> Result<()> {
    let uart = transport.uart("console")?;

    log::info!("Emulating start with bit-banging");
    let gpio_bitbanging = transport.gpio_bitbanging()?;
    let i2c_bitbang = test_utils::bitbanging::i2c::encoder::Encoder::<0, 1> {};

    const REFERENCE_DATA: &[u8] = b"Hello World!";
    let broken_byte = [
        test_utils::bitbanging::Bit::High,
        test_utils::bitbanging::Bit::Low,
        test_utils::bitbanging::Bit::Low,
        test_utils::bitbanging::Bit::High,
    ]
    .into_iter()
    .collect();

    let transaction = &i2c_bitbang.run(&[
        test_utils::bitbanging::i2c::encoder::Transfer::Start,
        test_utils::bitbanging::i2c::encoder::Transfer::Broken(broken_byte),
        test_utils::bitbanging::i2c::encoder::Transfer::Start,
        test_utils::bitbanging::i2c::encoder::Transfer::Addr {
            addr: address,
            read: false,
            nack: true,
        },
        test_utils::bitbanging::i2c::encoder::Transfer::Write(REFERENCE_DATA),
        test_utils::bitbanging::i2c::encoder::Transfer::Stop,
    ]);
    let waveform = Box::new([BitbangEntry::Write(transaction)]);

    log::info!("Testing write transaction at I2C address {address:02x}");
    let transfer = I2cTransferStart::execute_write(&*uart, || {
        gpio_bitbanging.run(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
            Duration::from_micros(10),
            waveform,
        )?;
        Ok(())
    })?;

    let len = transfer.length as usize;
    assert_eq!(&transfer.data[0..len], REFERENCE_DATA);
    assert_eq!(transfer.address, address);
    Ok(())
}

fn test_write_read_repeated_start(
    _opts: &Opts,
    transport: &TransportWrapper,
    address: u8,
    gpio_pins: &[Rc<dyn GpioPin>],
) -> Result<()> {
    let uart = transport.uart("console")?;

    let gpio_bitbanging = transport.gpio_bitbanging()?;
    let i2c_bitbang_encoder = test_utils::bitbanging::i2c::encoder::Encoder::<0, 1> {};
    let mut i2c_bitbang_decoder =
        test_utils::bitbanging::i2c::decoder::Decoder::<0, 1> { buffer: [0; 256] };

    const WRITE_REFERENCE_DATA: &[u8] = b"Sending Hello!";
    const READ_REFERENCE_DATA: &[u8] = b"Receiving Hello!";

    // This test verifies that the i2c target can do a write and read operation within the same
    // transaction with repeated start.
    let mut transfer = i2c_bitbang_encoder
        .run(&[
            test_utils::bitbanging::i2c::encoder::Transfer::Start,
            test_utils::bitbanging::i2c::encoder::Transfer::Addr {
                addr: address,
                read: false,
                nack: true,
            },
            test_utils::bitbanging::i2c::encoder::Transfer::Write(WRITE_REFERENCE_DATA),
            test_utils::bitbanging::i2c::encoder::Transfer::Start,
            test_utils::bitbanging::i2c::encoder::Transfer::Addr {
                addr: address,
                read: true,
                nack: false,
            },
            test_utils::bitbanging::i2c::encoder::Transfer::Read(READ_REFERENCE_DATA.len()),
            test_utils::bitbanging::i2c::encoder::Transfer::Stop,
        ])
        .to_vec();

    // Extend the number of samples to make sure that the stop bit will be captured in the read buffer.
    transfer.extend([0x03; 5]);
    let mut buffer = vec![0u8; transfer.len()];
    let waveform = Box::new([BitbangEntry::Both(&transfer, &mut buffer)]);

    log::info!("Testing write transaction at I2C address 0x{address:02x}");
    let txn = I2cTransferStart::new(address, READ_REFERENCE_DATA, false);
    let _ = txn.execute_write_read(&*uart, || {
        gpio_bitbanging.run(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
            Duration::from_micros(10),
            waveform,
        )?;
        Ok(())
    })?;

    let decoded = i2c_bitbang_decoder.run(buffer)?;
    let read: Vec<_> = decoded
        .into_iter()
        .skip_while(|x| match x {
            test_utils::bitbanging::i2c::decoder::Transfer::Addr {
                addr,
                read,
                nack: _,
            } => !(*addr == address && *read),
            _ => true,
        })
        .skip(1)
        .collect();

    assert_eq!(
        *read.first().unwrap(),
        test_utils::bitbanging::i2c::decoder::Transfer::Bytes {
            data: READ_REFERENCE_DATA,
            nack: true
        }
    );
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;
    uart.clear_rx_buffer()?;

    for i2c_instance in 0..3 {
        execute_test!(test_set_target_address, &opts, &transport, i2c_instance);
        execute_test!(test_read_transaction, &opts, &transport, 0x33);
        execute_test!(test_read_transaction, &opts, &transport, 0x70);
        execute_test!(test_read_transaction, &opts, &transport, 0x71);
        execute_test!(test_read_transaction, &opts, &transport, 0x72);
        execute_test!(test_clock_stretching, &opts, &transport, 0x72);
        execute_test!(test_read_transaction, &opts, &transport, 0x73);
        execute_test!(test_write_transaction, &opts, &transport, 0x33);
        execute_test!(test_write_transaction_slow, &opts, &transport, 0x33);
    }
    execute_test!(test_wakeup_normal_sleep, &opts, &transport, 0x33);
    execute_test!(test_wakeup_deep_sleep, &opts, &transport, 0x33, 0);

    transport.pin_strapping("RESET")?.apply()?;
    transport.pin_strapping("RESET")?.remove()?;
    UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    // The hyperdebug board does not like that pins mode are constantly changed,
    // so this commit separate the sub-tests that use the hyperdebug i2c from
    // the ones that do gpio bitbanging in order the make the test more
    // reliable.

    let gpio_pins = transport.gpio_pins(&["IOA7", "IOA8"].map(|s| s.to_string()))?;
    for pin in &gpio_pins {
        pin.set_mode(PinMode::OpenDrain)?;
    }
    for i2c_instance in 0..3 {
        execute_test!(test_set_target_address, &opts, &transport, i2c_instance);
        execute_test!(
            test_write_repeated_start,
            &opts,
            &transport,
            0x33,
            &gpio_pins
        );
        execute_test!(
            test_write_read_repeated_start,
            &opts,
            &transport,
            0x33,
            &gpio_pins
        );
    }
    Ok(())
}
