// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{anyhow, Result};
use clap::Parser;

use std::rc::Rc;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_svc::BootSlot;
use opentitanlib::io::uart::Uart;
use opentitanlib::rescue::xmodem::XmodemError;
use opentitanlib::rescue::{EntryMode, Rescue, RescueMode, RescueSerial};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

const POLYNOMIAL: u16 = 0x1021;
const CRC: u8 = 0x43;
const SOH: u8 = 0x01;
const STX: u8 = 0x02;
const EOF: u8 = 0x04;
const ACK: u8 = 0x06;
const NAK: u8 = 0x15;
const CAN: u8 = 0x18;

const BLOCK128_LEN: usize = 128;
const CRC_LEN: usize = 2;
const HEADER_LEN: usize = 3;

fn send_packet_timeout(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::Rescue)?;
    let mut ch = 0u8;
    uart.read(std::slice::from_mut(&mut ch))?;
    assert_eq!(ch, CRC);

    uart.write(&[STX])?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn send_data_timeout(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::Rescue)?;
    let mut ch = 0u8;
    uart.read(std::slice::from_mut(&mut ch))?;
    assert_eq!(ch, CRC);

    uart.write(&[STX, 1, 254])?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn send_crc_timeout(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::Rescue)?;
    let mut ch = 0u8;
    uart.read(std::slice::from_mut(&mut ch))?;
    assert_eq!(ch, CRC);

    let mut buf = vec![0xff; HEADER_LEN + BLOCK128_LEN];
    buf[0] = SOH;
    buf[1] = 1;
    buf[2] = 255 - buf[1];
    uart.write(&buf)?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn send_data_crc_error_cancel(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::Rescue)?;
    let mut ch = 0u8;
    uart.read(std::slice::from_mut(&mut ch))?;
    assert_eq!(ch, CRC);
    let mut buf = vec![0xff; HEADER_LEN + BLOCK128_LEN + CRC_LEN];
    buf[0] = SOH;
    buf[1] = 1;
    buf[2] = 255 - buf[1];
    uart.write(&buf)?;
    let mut ch = 0u8;
    uart.read(std::slice::from_mut(&mut ch))?;
    assert_eq!(ch, NAK);
    buf[1] = buf[2];
    uart.write(&buf)?;
    uart.read(std::slice::from_mut(&mut ch))?;
    assert_eq!(ch, CAN);

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn send_packet_bad_len(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::Rescue)?;
    let mut ch = 0u8;
    uart.read(std::slice::from_mut(&mut ch))?;
    assert_eq!(ch, CRC);

    let buf_1k = vec![0xff; 1024];
    let buf_128 = vec![0xff; 128];

    uart.write(&[STX, 1, 254])?;
    uart.write(&buf_1k)?;
    let crc = crc16(&buf_1k[..]);
    uart.write(&[(crc >> 8) as u8, (crc & 0xFF) as u8])?;
    let mut ch = 0u8;
    uart.read(std::slice::from_mut(&mut ch))?;

    uart.write(&[SOH, 2, 253])?;
    uart.write(&buf_128)?;
    let crc = crc16(&buf_128[..]);
    uart.write(&[(crc >> 8) as u8, (crc & 0xFF) as u8])?;
    uart.read(std::slice::from_mut(&mut ch))?;

    uart.write(&[STX, 3, 252])?;
    uart.write(&buf_1k)?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn recv_start_timeout(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::BootLog)?;
    let buf = vec![0xff; 29];
    uart.write(&buf)?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn recv_start_cancel(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::BootLog)?;
    uart.write(&[CAN, CAN])?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn recv_start_nak(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::BootLog)?;
    uart.write(&[NAK, NAK])?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn recv_data_timeout(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::BootLog)?;
    uart.write(&[CRC])?;
    uart.write(&[NAK])?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn recv_data_cancel(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::BootLog)?;
    uart.write(&[CRC])?;
    uart.write(&[CAN, CAN])?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn recv_data_nak(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::BootLog)?;
    uart.write(&[CRC])?;
    uart.write(&[NAK, NAK])?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn crc16(buf: &[u8]) -> u16 {
    let mut crc = 0u16;
    for byte in buf {
        crc ^= (*byte as u16) << 8;
        for _bit in 0..8 {
            let msb = crc & 0x8000 != 0;
            crc <<= 1;
            if msb {
                crc ^= POLYNOMIAL;
            }
        }
    }
    crc
}

fn recv_finish_nak(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::BootLog)?;

    // Send the byte indicating the protocol we want (Xmodem-CRC).
    uart.write(&[CRC])?;

    let mut block = 1u8;
    let mut errors = 0usize;
    loop {
        // The first byte of the packet is the packet type which indicates the block size.
        let mut byte = 0u8;
        uart.read(std::slice::from_mut(&mut byte))?;
        let block_len = match byte {
            SOH => 128,
            STX => 1024,
            EOF => {
                // End of file. Intentionally send a NAK rather than ACK.
                uart.write(&[NAK])?;
                break;
            }
            _ => {
                return Err(XmodemError::UnsupportedMode(format!(
                    "bad start of packet: {byte:02x} ({})",
                    byte as char
                ))
                .into());
            }
        };

        // The next two bytes are the block number and its complement.
        let mut bnum = 0u8;
        let mut bcom = 0u8;
        uart.read(std::slice::from_mut(&mut bnum))?;
        uart.read(std::slice::from_mut(&mut bcom))?;
        let cancel = block != bnum || bnum != 255 - bcom;

        // The next `block_len` bytes are the packet itself.
        let mut buffer = vec![0; block_len];
        let mut total = 0;
        while total < block_len {
            let n = uart.read(&mut buffer[total..])?;
            total += n;
        }

        // The final two bytes are the CRC16.
        let mut crc1 = 0u8;
        let mut crc2 = 0u8;
        uart.read(std::slice::from_mut(&mut crc1))?;
        uart.read(std::slice::from_mut(&mut crc2))?;
        let crc = u16::from_be_bytes([crc1, crc2]);

        // If we should cancel, do it now.
        if cancel {
            uart.write(&[CAN, CAN])?;
            return Err(XmodemError::Cancelled.into());
        }
        if crc16(&buffer) == crc {
            // CRC was good; send an ACK
            uart.write(&[ACK])?;
            block = block.wrapping_add(1);
        } else {
            uart.write(&[NAK])?;
            errors += 1;
        }
        if errors >= 2 {
            return Err(XmodemError::ExhaustedRetries(errors).into());
        }
    }
    rescue.reboot()?;

    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn rescue_image_too_big(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    rescue: &RescueSerial,
) -> Result<()> {
    rescue.enter(transport, EntryMode::Reset)?;
    let image_too_big = [0u8; 1026*1024];
    match rescue.update_firmware(BootSlot::SlotB, &image_too_big) {
        Ok(_) => {
            return Err(anyhow!("Expects cancel during firmware rescue, but got OK."));
        }
        Err(e) => {
            if e.to_string().contains("Cancelled") {
                log::info!("Operation cancelled by device as expected");
            } else {
                return Err(e);
            }
        }
    };
    // Check for kErrorRescueImageTooBig.
    UartConsole::wait_for(uart, r"BFV:02525309", Duration::from_secs(5))?;
    // Ensure we can still boot into Owner SW.
    UartConsole::wait_for(uart, r"Finished", Duration::from_secs(5))?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    let uart = transport.uart("console")?;
    let rescue = RescueSerial::new(Rc::clone(&uart), None);
    send_packet_timeout(&transport, &*uart, &rescue)?;
    send_data_timeout(&transport, &*uart, &rescue)?;
    send_crc_timeout(&transport, &*uart, &rescue)?;
    send_data_crc_error_cancel(&transport, &*uart, &rescue)?;
    send_packet_bad_len(&transport, &*uart, &rescue)?;
    recv_start_timeout(&transport, &*uart, &rescue)?;
    recv_start_cancel(&transport, &*uart, &rescue)?;
    recv_start_nak(&transport, &*uart, &rescue)?;
    recv_data_timeout(&transport, &*uart, &rescue)?;
    recv_data_cancel(&transport, &*uart, &rescue)?;
    recv_data_nak(&transport, &*uart, &rescue)?;
    recv_finish_nak(&transport, &*uart, &rescue)?;
    rescue_image_too_big(&transport, &*uart, &rescue)?;
    Ok(())
}
