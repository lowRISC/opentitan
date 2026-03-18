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

use rusb::{Direction, Error, Recipient, RequestType};
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
    UartEcho,
    EpConfig,
}

const TIMEOUT: Duration = Duration::from_secs(5);
const RQTYPE: u8 = rusb::request_type(Direction::In, RequestType::Vendor, Recipient::Device);

const USB_STATUS_SELF_POWERED: u16 = 1;
const USB_STATUS_HALTED: u16 = 1;
const USB_FEATURE_ENDPOINT_HALT: u16 = 0;

const EP_OUT_00: u8 = 0x00;
const EP_IN_00: u8 = 0x80;
const EP_OUT_01: u8 = 0x01;
const EP_IN_02: u8 = 0x82;
const EP_OUT_0F: u8 = 0x0F;

impl TestReq {
    fn randomize(dev: &UsbDeviceHandle) -> Result<()> {
        dev.read_control(RQTYPE, TestReq::Randomize as u8, 0, 0, &mut [], TIMEOUT)?;
        Ok(())
    }

    fn digest(dev: &UsbDeviceHandle, length: u16, data: &mut [u8]) -> Result<()> {
        dev.read_control(RQTYPE, TestReq::Digest as u8, length, 0, data, TIMEOUT)?;
        Ok(())
    }

    fn bulk_in(dev: &UsbDeviceHandle, length: u16, ep: u8) -> Result<()> {
        dev.read_control(
            RQTYPE,
            TestReq::BulkIn as u8,
            length,
            ep as u16,
            &mut [],
            TIMEOUT,
        )?;
        Ok(())
    }

    fn bulk_out(dev: &UsbDeviceHandle, length: u16, ep: u8) -> Result<()> {
        dev.read_control(
            RQTYPE,
            TestReq::BulkOut as u8,
            length,
            ep as u16,
            &mut [],
            TIMEOUT,
        )?;
        Ok(())
    }

    fn exit(dev: &UsbDeviceHandle) -> Result<()> {
        dev.read_control(RQTYPE, TestReq::Exit as u8, 0, 0, &mut [], TIMEOUT)?;
        Ok(())
    }

    fn uart_echo(dev: &UsbDeviceHandle, id: u16) -> Result<()> {
        dev.read_control(RQTYPE, TestReq::UartEcho as u8, id, 0, &mut [], TIMEOUT)?;
        Ok(())
    }

    fn ep_config(dev: &UsbDeviceHandle, ep: u8, use_handler: bool) -> Result<()> {
        dev.read_control(
            RQTYPE,
            TestReq::EpConfig as u8,
            use_handler as u16,
            ep as u16,
            &mut [],
            TIMEOUT,
        )?;
        Ok(())
    }
}

fn ep_name(ep: u8) -> String {
    if ep & rusb::constants::LIBUSB_ENDPOINT_IN != 0 {
        format!("IN EP 0x{:x}", ep & 0xf)
    } else {
        format!("OUT EP 0x{:x}", ep & 0xf)
    }
}

fn receive_random_buffer(dev: &UsbDeviceHandle, short_len: Option<usize>) -> Result<()> {
    let mut buffer = vec![0u8; 65536];
    // Determine if the test requests a shorter length than the full buffer length.
    // We pass this (possibly short) length in the `value` field of the control transactions
    // to indicate to the DUT the actual length.
    // We compute the length minus one because the `value` field is a u16 and we have a
    // maximum size of 65536.
    let length = (short_len.unwrap_or(buffer.len()) - 1) as u16;

    // Randomize the device buffer and get the device's digest of the buffer.
    TestReq::randomize(dev)?;
    let mut dev_digest = [0u8; 32];
    TestReq::digest(dev, length, &mut dev_digest)?;

    // Transfer the buffer from device to host.
    let ep = EP_IN_02;
    log::info!("Starting bulk transfer");
    TestReq::bulk_in(dev, length, ep)?;
    let t0 = Instant::now();

    // Attempt to receive the full 64K buffer.  For shorter transactions, this
    // tests the DUT properly finishes short transactions.
    let len = dev.read_bulk(ep, &mut buffer, TIMEOUT)?;
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
    let ep = EP_OUT_01;
    TestReq::bulk_out(dev, (buffer.len() - 1) as u16, ep)?;
    // Write the (possibly short) buffer to the device.
    let t0 = Instant::now();
    let slice = &buffer[0..(length as usize + 1)];
    let len = dev.write_bulk(ep, slice, TIMEOUT)?;
    if len < buffer.len() && len % 64 == 0 {
        // If the transfer was a multiple of the endpoint size, send a
        // zero-length transfer to finish the transaction.
        dev.write_bulk(ep, &[], TIMEOUT)?;
    }
    let t1 = Instant::now();
    log::info!("Sent {len} bytes in {}us", (t1 - t0).as_micros());
    let buf_digest = Sha256Digest::hash(slice);
    let mut dev_digest = [0u8; 32];
    TestReq::digest(dev, length, &mut dev_digest)?;
    log::info!("DevDigest = {}", hex::encode(dev_digest));
    log::info!("BufDigest = {}", hex::encode(buf_digest.as_ref()));
    assert_eq!(len, length as usize + 1);
    assert_eq!(dev_digest, buf_digest.as_ref());
    Ok(())
}

fn test_device_descriptor(dev: &UsbDeviceHandle) -> Result<()> {
    let desc = dev.device().device_descriptor()?;
    assert_eq!(desc.vendor_id(), 0x18d1);
    assert_eq!(desc.product_id(), 0x503a);
    assert_eq!(desc.num_configurations(), 1);
    assert_eq!(desc.manufacturer_string_index(), Some(1));
    assert_eq!(desc.product_string_index(), Some(2));
    assert_eq!(desc.serial_number_string_index(), Some(3));
    Ok(())
}

fn test_config_descriptor(dev: &UsbDeviceHandle) -> Result<()> {
    let desc = dev.device().config_descriptor(0)?;
    assert_eq!(desc.num_interfaces(), 1);
    assert_eq!(desc.total_length(), 32);
    assert_eq!(desc.number(), 1);
    assert!(desc.self_powered());
    assert_eq!(desc.max_power(), 100); // 50 * 2mA = 100mA

    let iface = desc.interfaces().next().unwrap();
    let iface_desc = iface.descriptors().next().unwrap();
    assert_eq!(iface_desc.interface_number(), 1);
    assert_eq!(iface_desc.num_endpoints(), 2);
    assert_eq!(iface_desc.class_code(), 0xFF);
    assert_eq!(iface_desc.sub_class_code(), 0xFF);
    assert_eq!(iface_desc.protocol_code(), 1);

    let mut eps = iface_desc.endpoint_descriptors();
    let ep1 = eps.next().unwrap();
    assert_eq!(ep1.address(), EP_OUT_01);
    assert_eq!(ep1.max_packet_size(), 64);

    let ep2 = eps.next().unwrap();
    assert_eq!(ep2.address(), EP_IN_02);
    assert_eq!(ep2.max_packet_size(), 64);

    Ok(())
}

fn test_string_descriptors(dev: &UsbDeviceHandle) -> Result<()> {
    let languages = dev.read_languages(TIMEOUT)?;
    log::info!("Supported languages: {:?}", languages);
    assert!(!languages.is_empty());
    let lang = languages[0];

    let desc = dev.device().device_descriptor()?;

    let manufacturer = dev.read_manufacturer_string_ascii(&desc)?;
    log::info!("Manufacturer: {}", manufacturer);
    assert_eq!(manufacturer, "Google");

    let product = dev.read_product_string_ascii(&desc)?;
    log::info!("Product: {}", product);
    assert_eq!(product, "OpenTitan");

    let serial = dev.read_serial_number_string_ascii(&desc)?;
    log::info!("Serial: {}", serial);
    assert!(!serial.is_empty(), "expected non-empty serial number");

    // Test with language
    let manufacturer_lang = dev.read_manufacturer_string(lang, &desc, TIMEOUT)?;
    assert_eq!(manufacturer_lang, manufacturer);

    let product_lang = dev.read_product_string(lang, &desc, TIMEOUT)?;
    assert_eq!(product_lang, product);

    let serial_lang = dev.read_serial_number_string(lang, &desc, TIMEOUT)?;
    assert_eq!(serial_lang, serial);

    Ok(())
}

fn test_string_descriptor_invalid(dev: &UsbDeviceHandle) -> Result<()> {
    let res = dev.read_string_descriptor_ascii(0x42);
    assert!(
        matches!(res, Err(Error::Pipe)),
        "expected Pipe error when requesting invalid string descriptor, got {:?}",
        res
    );
    Ok(())
}

fn test_get_status(dev: &UsbDeviceHandle) -> Result<()> {
    let mut buffer = [0u8; 2];

    log::info!("Testing GetStatus (Device)");
    dev.read_control(
        rusb::request_type(Direction::In, RequestType::Standard, Recipient::Device),
        rusb::constants::LIBUSB_REQUEST_GET_STATUS,
        0,
        0,
        &mut buffer,
        TIMEOUT,
    )?;
    let status = u16::from_le_bytes(buffer);
    assert_eq!(
        status, USB_STATUS_SELF_POWERED,
        "unexpected device status (expected self-powered, got {:04x})",
        status
    );

    for ep in [EP_OUT_00, EP_IN_00, EP_OUT_01, EP_IN_02] {
        log::info!("Testing GetStatus ({})", ep_name(ep));
        dev.read_control(
            rusb::request_type(Direction::In, RequestType::Standard, Recipient::Endpoint),
            rusb::constants::LIBUSB_REQUEST_GET_STATUS,
            0,
            ep as u16,
            &mut buffer,
            TIMEOUT,
        )?;
        let status = u16::from_le_bytes(buffer);
        assert_eq!(
            status,
            0,
            "unexpected endpoint status for {} (expected 0, got {:04x})",
            ep_name(ep),
            status
        );
    }

    log::info!("Testing GetStatus (Other)");
    let res = dev.read_control(
        rusb::request_type(Direction::In, RequestType::Standard, Recipient::Other),
        rusb::constants::LIBUSB_REQUEST_GET_STATUS,
        0,
        0,
        &mut buffer,
        TIMEOUT,
    );
    assert!(
        matches!(res, Err(Error::Pipe)),
        "expected Pipe error when requesting status for unsupported recipient, got {:?}",
        res
    );

    log::info!("Testing GetStatus (Interface)");
    let res = dev.read_control(
        rusb::request_type(Direction::In, RequestType::Standard, Recipient::Interface),
        rusb::constants::LIBUSB_REQUEST_GET_STATUS,
        0,
        1, // Claimed interface
        &mut buffer,
        TIMEOUT,
    );
    assert!(
        matches!(res, Err(Error::Pipe)),
        "expected Pipe error when requesting status for unsupported recipient (Interface), got {:?}",
        res
    );

    Ok(())
}

fn test_set_configuration(dev: &UsbDeviceHandle) -> Result<()> {
    let mut buffer = [0u8; 1];
    log::info!("Testing SetConfiguration (unconfigured)");
    dev.release_interface(1)?;
    dev.reset()?;
    dev.unconfigure()?;
    // FIXME: Why dev.active_configuration() doesn't sent the setup packet?
    log::info!("Testing GetConfiguration (unconfigured)");
    dev.read_control(
        rusb::request_type(Direction::In, RequestType::Standard, Recipient::Device),
        rusb::constants::LIBUSB_REQUEST_GET_CONFIGURATION,
        0,
        0,
        &mut buffer,
        TIMEOUT,
    )?;
    assert_eq!(
        buffer[0], 0,
        "unexpected configuration response (expected {}, got {})",
        0, buffer[0]
    );

    let config = 1;
    log::info!("SetConfiguration ({})", config);
    dev.reset()?;
    dev.set_active_configuration(config)?;

    // FIXME: Why dev.active_configuration() doesn't sent the setup packet?
    log::info!("GetConfiguration ({})", config);
    dev.read_control(
        rusb::request_type(Direction::In, RequestType::Standard, Recipient::Device),
        rusb::constants::LIBUSB_REQUEST_GET_CONFIGURATION,
        0,
        0,
        &mut buffer,
        TIMEOUT,
    )?;
    assert_eq!(
        buffer[0], config,
        "unexpected configuration response (expected {}, got {})",
        config, buffer[0]
    );

    dev.claim_interface(1)?;
    Ok(())
}

fn test_set_interface(dev: &UsbDeviceHandle) -> Result<()> {
    let mut buffer = [0x42u8; 1];
    let iface = 1u8;
    let alt_setting = 0u8;
    log::info!("SetInterface (iface={}, alt={})", iface, alt_setting);
    dev.set_alternate_setting(iface, alt_setting)?;

    log::info!("GetInterface (iface={})", iface);
    dev.read_control(
        rusb::request_type(Direction::In, RequestType::Standard, Recipient::Interface),
        rusb::constants::LIBUSB_REQUEST_GET_INTERFACE,
        0,
        iface as u16,
        &mut buffer,
        TIMEOUT,
    )?;
    let response = buffer[0];
    assert_eq!(
        response, alt_setting,
        "unexpected interface response (expected {}, got {:04x})",
        alt_setting, response
    );
    Ok(())
}

fn test_feature_halt(dev: &UsbDeviceHandle) -> Result<()> {
    let mut buffer = [0u8; 2];

    for ep in [EP_OUT_01, EP_IN_02] {
        log::info!("Testing SetFeature (Halt) {}", ep_name(ep));
        dev.write_control(
            rusb::request_type(Direction::Out, RequestType::Standard, Recipient::Endpoint),
            rusb::constants::LIBUSB_REQUEST_SET_FEATURE,
            USB_FEATURE_ENDPOINT_HALT,
            ep as u16,
            &[],
            TIMEOUT,
        )?;

        log::info!("Verifying {} is halted", ep_name(ep));
        dev.read_control(
            rusb::request_type(Direction::In, RequestType::Standard, Recipient::Endpoint),
            rusb::constants::LIBUSB_REQUEST_GET_STATUS,
            0,
            ep as u16,
            &mut buffer,
            TIMEOUT,
        )?;
        let status = u16::from_le_bytes(buffer);
        assert_eq!(
            status,
            USB_STATUS_HALTED,
            "expected {} to be halted (status={:04x})",
            ep_name(ep),
            status
        );

        log::info!("Testing ClearFeature (Halt) {}", ep_name(ep));
        dev.clear_halt(ep)?;

        log::info!("Verifying {} is NOT halted", ep_name(ep));
        dev.read_control(
            rusb::request_type(Direction::In, RequestType::Standard, Recipient::Endpoint),
            rusb::constants::LIBUSB_REQUEST_GET_STATUS,
            0,
            ep as u16,
            &mut buffer,
            TIMEOUT,
        )?;
        let status = u16::from_le_bytes(buffer);
        assert_eq!(
            status,
            0,
            "expected {} NOT to be halted (status={:04x})",
            ep_name(ep),
            status
        );
    }

    Ok(())
}

fn test_set_feature_unsupported(dev: &UsbDeviceHandle) -> Result<()> {
    let res = dev.write_control(
        rusb::request_type(Direction::Out, RequestType::Standard, Recipient::Device),
        rusb::constants::LIBUSB_REQUEST_SET_FEATURE,
        0xbeef,
        0,
        &[],
        TIMEOUT,
    );
    assert!(
        matches!(res, Err(Error::Pipe)),
        "expected Pipe error when setting unsupported feature, got {:?}",
        res
    );
    Ok(())
}

fn test_clear_feature_unsupported(dev: &UsbDeviceHandle) -> Result<()> {
    let res = dev.write_control(
        rusb::request_type(Direction::Out, RequestType::Standard, Recipient::Device),
        rusb::constants::LIBUSB_REQUEST_CLEAR_FEATURE,
        0xbeef,
        0,
        &[],
        TIMEOUT,
    );
    assert!(
        matches!(res, Err(Error::Pipe)),
        "expected Pipe error when clearing unsupported feature, got {:?}",
        res
    );
    Ok(())
}

fn test_synch_frame(dev: &UsbDeviceHandle) -> Result<()> {
    let mut buffer = [0u8; 2];
    dev.read_control(
        rusb::request_type(Direction::In, RequestType::Standard, Recipient::Endpoint),
        rusb::constants::LIBUSB_REQUEST_SYNCH_FRAME,
        0,
        EP_IN_02 as u16,
        &mut buffer,
        TIMEOUT,
    )?;
    Ok(())
}

fn test_std_cmd_unsupported(dev: &UsbDeviceHandle) -> Result<()> {
    let mut buffer = [0u8; 256];
    let res = dev.read_control(
        rusb::request_type(Direction::In, RequestType::Standard, Recipient::Device),
        0xFF,
        0,
        0,
        &mut buffer,
        TIMEOUT,
    );
    assert!(
        matches!(res, Err(Error::Pipe)),
        "expected Pipe error for unsupported standard request, got {:?}",
        res
    );
    Ok(())
}

fn test_ep_config_invalid_ep(dev: &UsbDeviceHandle) -> Result<()> {
    TestReq::ep_config(dev, EP_OUT_0F, false)?;
    Ok(())
}

fn test_bulk_out_invalid_ep(dev: &UsbDeviceHandle) -> Result<()> {
    TestReq::bulk_out(dev, 0, EP_OUT_0F)?;
    Ok(())
}

fn test_zlp_transfer(dev: &UsbDeviceHandle) -> Result<()> {
    let buffer = [0xAA, 0xBB, 0xCC, 0xDD];
    dev.write_control(
        rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Device),
        TestReq::BulkOut as u8,
        buffer.len() as u16,
        EP_OUT_00 as u16,
        &buffer,
        TIMEOUT,
    )?;
    Ok(())
}

fn test_out_null_handler(dev: &UsbDeviceHandle) -> Result<()> {
    let ep = EP_OUT_01;
    let buffer = [0x11, 0x22, 0x33, 0x44];
    log::info!("Re-initialize with NULL handler");
    TestReq::ep_config(dev, ep, false)?;

    log::info!("Testing OUT NULL handler");
    TestReq::bulk_out(dev, buffer.len() as u16, ep)?;

    dev.write_bulk(ep, &buffer, TIMEOUT)?;

    log::info!("Restoring handler");
    TestReq::ep_config(dev, ep, true)?;
    Ok(())
}

fn test_in_null_handler(dev: &UsbDeviceHandle) -> Result<()> {
    let ep = EP_IN_02;
    log::info!("Re-initialize with NULL handler");
    TestReq::ep_config(dev, ep, false)?;

    log::info!("Testing IN NULL handler");
    receive_random_buffer(dev, None)?;
    receive_random_buffer(dev, Some(65535))?;
    receive_random_buffer(dev, Some(65536 - 64))?;

    log::info!("Restoring handler");
    TestReq::ep_config(dev, ep, true)?;
    Ok(())
}

fn test_in_overflow(dev: &UsbDeviceHandle) -> Result<()> {
    // Tell DUT to send 64 bytes on EP2.
    TestReq::bulk_in(dev, 63, EP_IN_02)?;

    let mut buffer = [0u8; 8];
    let res = dev.read_bulk(EP_IN_02, &mut buffer, TIMEOUT);
    log::info!("Expected Overflow error: {:?}", res);
    assert!(
        matches!(res, Err(Error::Overflow)),
        "expected Overflow error, got {:?}",
        res
    );
    Ok(())
}

fn test_out_overflow(dev: &UsbDeviceHandle, uart: &dyn opentitanlib::io::uart::Uart) -> Result<()> {
    let ep = EP_OUT_01;
    let buffer = vec![0u8; 64];
    // Tell DUT to expect 8 bytes on EP1
    TestReq::bulk_out(dev, 7, ep)?;
    // Send 64 bytes
    dev.write_bulk(ep, &buffer, TIMEOUT)?;
    UartConsole::wait_for(uart, &format!("USB Error on EP0x{:02x}", ep), TIMEOUT)?;
    Ok(())
}

fn test_usb_reset(dev: &UsbDeviceHandle, uart: &dyn opentitanlib::io::uart::Uart) -> Result<()> {
    dev.reset()?;
    UartConsole::wait_for(uart, r"USB Reset on EP0x00", TIMEOUT)?;
    Ok(())
}

fn test_reset_during_in(
    dev: &UsbDeviceHandle,
    uart: &dyn opentitanlib::io::uart::Uart,
) -> Result<()> {
    // Start a large IN transfer on EP2
    TestReq::bulk_in(dev, 0x3FFF, EP_IN_02)?;
    // Reset the device while transfer is likely pending
    dev.reset()?;
    UartConsole::wait_for(uart, r"USB Reset on EP0x00", TIMEOUT)?;
    Ok(())
}

fn test_exit(dev: &UsbDeviceHandle) -> Result<()> {
    TestReq::exit(dev)?;
    Ok(())
}

fn sync_uart(
    dev: &UsbDeviceHandle,
    uart: &dyn opentitanlib::io::uart::Uart,
    id: u16,
) -> Result<()> {
    TestReq::uart_echo(dev, id)?;
    UartConsole::wait_for(uart, &format!("USB UartEcho 0x{:x}", id), TIMEOUT)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Wait until test is running.
    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"usb ready", opts.timeout)?;

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

    let mut sync_id = 0u16;
    let next_sync = |dev: &UsbDeviceHandle, id: &mut u16| -> Result<()> {
        *id += 1;
        sync_uart(dev, &*uart, *id)
    };

    next_sync(&device, &mut sync_id)?;
    execute_test!(receive_random_buffer, &device, None);
    next_sync(&device, &mut sync_id)?;
    execute_test!(receive_random_buffer, &device, Some(65535));
    next_sync(&device, &mut sync_id)?;
    execute_test!(receive_random_buffer, &device, Some(65536 - 64));
    next_sync(&device, &mut sync_id)?;
    execute_test!(send_random_buffer, &device, None);
    next_sync(&device, &mut sync_id)?;
    execute_test!(send_random_buffer, &device, Some(65535));
    next_sync(&device, &mut sync_id)?;
    execute_test!(send_random_buffer, &device, Some(65536 - 64));
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_device_descriptor, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_config_descriptor, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_string_descriptors, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_string_descriptor_invalid, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_get_status, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_set_configuration, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_set_interface, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_feature_halt, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_set_feature_unsupported, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_clear_feature_unsupported, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_synch_frame, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_std_cmd_unsupported, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_ep_config_invalid_ep, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_bulk_out_invalid_ep, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_zlp_transfer, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_out_null_handler, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_in_null_handler, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_in_overflow, &device);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_out_overflow, &device, &*uart);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_usb_reset, &device, &*uart);
    next_sync(&device, &mut sync_id)?;
    execute_test!(test_reset_during_in, &device, &*uart);
    next_sync(&device, &mut sync_id)?;
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
