// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail, ensure};
use clap::Parser;
use rand::prelude::*;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

use rusb::{Direction, Recipient, RequestType};
use usb::{UsbDeviceHandle, UsbOpts, port_path_string};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console/USB timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "60s")]
    timeout: Duration,

    /// USB options.
    #[command(flatten)]
    usb: UsbOpts,

    /// Do not wait for USB device to appear before continuing with the test.
    #[arg(long, default_value_t = false)]
    no_wait_for_usb_device: bool,

    /// Executable to run after USB device connection.
    /// This harness will spawn a process to execute and continue monitoring the UART
    /// until the test passes (or fails). After that, the process will be killed.
    /// Unless `no_wait_for_usb_device` is set, the harness will pass two extra arguments
    /// to the executable to specify the bus and address of the USB device, as follows:
    /// `--devide <bus>:<addr>`.
    #[arg(long)]
    exec: Option<PathBuf>,

    /// Arguments to pass to the executable.
    #[arg(long)]
    exec_arg: Vec<std::ffi::OsString>,
}

fn wait_for_device(opts: &Opts) -> Result<UsbDeviceHandle> {
    log::info!("waiting for device...");
    let mut devices = opts.usb.wait_for_device(opts.timeout)?;
    if devices.is_empty() {
        bail!("no USB device found");
    }
    if devices.len() > 1 {
        log::error!("several USB devices found:");
        for dev in devices {
            log::error!(
                "- bus={} address={}",
                dev.device().bus_number(),
                dev.device().address()
            );
        }
        bail!("several USB devices found");
    }
    let device = devices.remove(0);
    log::info!(
        "device found at bus={}, address={}, path={}",
        device.device().bus_number(),
        device.device().address(),
        port_path_string(&device.device())?
    );
    Ok(device)
}

#[repr(u8)]
#[allow(dead_code)]
enum TestReq {
    Randomize = 1,
    Digest,
    BulkIn,
    BulkOut,
    Exit,
}

const TIMEOUT: Duration = Duration::from_secs(5);
const RQTYPE: u8 = rusb::request_type(Direction::In, RequestType::Vendor, Recipient::Device);

fn receive_random_buffer(dev: &UsbDeviceHandle, short_len: Option<usize>) -> Result<()> {
    let mut buffer = vec![0u8; 65536];
    // Determine if the test requests a shorter length than the full buffer length.
    // We pass this (possibly short) length in the `value` field of the control transactions
    // to indicate to the DUT the actual length.
    // We compute the length minus one because the `value` field is a u16 and we have a
    // maximum size of 65536.
    let length = (short_len.unwrap_or(buffer.len()) - 1) as u16;

    // Randomize the device buffer and get the device's digest of the buffer.
    dev.read_control(RQTYPE, TestReq::Randomize as u8, 0, 0, &mut [], TIMEOUT)?;
    let mut dev_digest = [0u8; 32];
    dev.read_control(
        RQTYPE,
        TestReq::Digest as u8,
        length,
        0,
        &mut dev_digest,
        TIMEOUT,
    )?;

    // Transfer the buffer from device to host.
    log::info!("Starting bulk transfer");
    dev.read_control(RQTYPE, TestReq::BulkIn as u8, length, 2, &mut [], TIMEOUT)?;
    let t0 = Instant::now();

    // Attempt to receive the full 64K buffer.  For shorter transactions, this
    // tests the DUT properly finishes short transactions.
    let len = dev.read_bulk(0x82, &mut buffer, TIMEOUT)?;
    let t1 = Instant::now();
    log::info!("Received {len} bytes in {}us", (t1 - t0).as_micros());
    let buf_digest = Sha256Digest::hash(&buffer[..len]);
    log::info!("DevDigest = {}", hex::encode(dev_digest));
    log::info!("BufDigest = {}", hex::encode(buf_digest.as_ref()));
    assert_eq!(len, length as usize + 1);
    assert_eq!(dev_digest, buf_digest.as_ref());
    Ok(())
}

fn send_random_buffer(dev: &UsbDeviceHandle, short_len: Option<usize>) -> Result<()> {
    let mut buffer = vec![0u8; 65536];
    // Determine if the test requests a shorter length than the full buffer length.
    // We pass this (possibly short) length in the `value` field of the control transactions
    // to indicate to the DUT the actual length.
    // We compute the length minus one because the `value` field is a u16 and we have a
    // maximum size of 65536.
    let length = (short_len.unwrap_or(buffer.len()) - 1) as u16;
    let mut rng = rand::thread_rng();
    rng.fill_bytes(&mut buffer);

    // Tell the DUT that we will transfer 65536 bytes.  For short transactions,
    // this tests whether the DUT correctly understands shorter transactions.
    dev.read_control(
        RQTYPE,
        TestReq::BulkOut as u8,
        (buffer.len() - 1) as u16,
        1,
        &mut [],
        TIMEOUT,
    )?;
    // Write the (possibly short) buffer to the device.
    let t0 = Instant::now();
    let slice = &buffer[0..(length as usize + 1)];
    let len = dev.write_bulk(0x01, slice, TIMEOUT)?;
    if len < buffer.len() && len % 64 == 0 {
        // If the transfer was a multiple of the endpoint size, send a
        // zero-length transfer to finish the transaction.
        dev.write_bulk(0x01, &[], TIMEOUT)?;
    }
    let t1 = Instant::now();
    log::info!("Sent {len} bytes in {}us", (t1 - t0).as_micros());
    let buf_digest = Sha256Digest::hash(slice);
    let mut dev_digest = [0u8; 32];
    dev.read_control(
        RQTYPE,
        TestReq::Digest as u8,
        length,
        0,
        &mut dev_digest,
        TIMEOUT,
    )?;
    log::info!("DevDigest = {}", hex::encode(dev_digest));
    log::info!("BufDigest = {}", hex::encode(buf_digest.as_ref()));
    assert_eq!(len, length as usize + 1);
    assert_eq!(dev_digest, buf_digest.as_ref());
    Ok(())
}

fn test_exit(dev: &UsbDeviceHandle) -> Result<()> {
    dev.read_control(RQTYPE, TestReq::Exit as u8, 0, 0, &mut [], TIMEOUT)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Wait until test is running.
    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    // Enable VBUS sense on the board if necessary.
    if opts.usb.vbus_control_available() {
        opts.usb.enable_vbus(&transport, true)?;
    }
    // Sense VBUS if available.
    if opts.usb.vbus_sense_available() {
        ensure!(
            opts.usb.vbus_present(&transport)?,
            "OT USB does not appear to be connected to a host (VBUS not detected)"
        );
    }

    let device = wait_for_device(&opts)?;
    device.claim_interface(1)?;

    execute_test!(receive_random_buffer, &device, None);
    execute_test!(receive_random_buffer, &device, Some(65535));
    execute_test!(receive_random_buffer, &device, Some(65536 - 64));
    execute_test!(send_random_buffer, &device, None);
    execute_test!(send_random_buffer, &device, Some(65535));
    execute_test!(send_random_buffer, &device, Some(65536 - 64));
    test_exit(&device)?;

    // Wait for test to pass.
    log::info!("wait for pass...");
    let res = UartConsole::wait_for(&*uart, r"PASS|FAIL", opts.timeout)?;
    match res[0].as_str() {
        "PASS" => (),
        "FAIL" => bail!("device code reported a failure"),
        _ => (),
    };

    Ok(())
}
