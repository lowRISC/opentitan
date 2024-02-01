// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module provides a convenience wrapper around the firmware's C
// implementation of Xmodem so that its easy to write tests for that
// implementation.

use anyhow::{anyhow, Result};
use std::io::Write;

use opentitanlib::io::uart::Uart;
use opentitanlib::with_unknown;

use xmodem_testlib::*;

with_unknown! {
    pub enum XmodemResult: u32 {
        Ok = rom_error_kErrorOk,
        TimeoutStart = rom_error_kErrorXModemTimeoutStart,
        TimeoutPacket = rom_error_kErrorXModemTimeoutPacket,
        TimeoutData = rom_error_kErrorXModemTimeoutData,
        TimeoutCrc = rom_error_kErrorXModemTimeoutCrc,
        TimeoutAck = rom_error_kErrorXModemTimeoutAck,
        Crc = rom_error_kErrorXModemCrc,
        EndOfFile = rom_error_kErrorXModemEndOfFile,
        Cancel = rom_error_kErrorXModemCancel,
        Unknown = rom_error_kErrorXModemUnknown,
        Protocol = rom_error_kErrorXModemProtocol,
        TooManyErrors = rom_error_kErrorXModemTooManyErrors,
    }
}

#[derive(Default)]
pub struct XmodemFirmware {
    // Only relevant to the `receive` function.
    pub max_errors: usize,
}

impl XmodemFirmware {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn send(&self, uart: &dyn Uart, data: &[u8]) -> Result<()> {
        let result = unsafe {
            let io: *mut std::os::raw::c_void = std::mem::transmute(&uart as *const &dyn Uart);
            let buf = data.as_ptr() as *const std::os::raw::c_void;
            let len = data.len();
            XmodemResult(xmodem_send(io, buf, len))
        };
        match result {
            XmodemResult::Ok => Ok(()),
            _ => Err(anyhow!("{}", result)),
        }
    }

    pub fn receive(&self, uart: &dyn Uart, data: &mut impl Write) -> Result<()> {
        unsafe {
            let io: *mut std::os::raw::c_void = std::mem::transmute(&uart as *const &dyn Uart);
            xmodem_recv_start(io);

            let mut errors = 0;
            let mut frame = 1u32;
            let mut buf = [0u8; 1024];
            let mut rxlen = 0usize;
            let mut unknown_rx = 0u8;

            loop {
                let result = XmodemResult(xmodem_recv_frame(
                    io,
                    frame,
                    buf.as_mut_ptr(),
                    &mut rxlen as *mut usize,
                    &mut unknown_rx as *mut u8,
                ));

                match result {
                    XmodemResult::Ok => {
                        data.write_all(&buf[..rxlen])?;
                        xmodem_ack(io, true);
                        frame += 1;
                    }
                    XmodemResult::Crc => {
                        xmodem_ack(io, false);
                        errors += 1;
                        if errors >= self.max_errors {
                            return Err(anyhow!("{}", result));
                        }
                    }
                    XmodemResult::EndOfFile => {
                        xmodem_ack(io, true);
                        return Ok(());
                    }
                    _ => return Err(anyhow!("{}", result)),
                }
            }
        }
    }
}

// The xmodem_{read,write} functions provide the interface to the low-level C implementation to
// interact with the `Uart` device provided to the `XmodemFirmware` struct.
#[no_mangle]
extern "C" fn xmodem_read(
    iohandle: *mut std::os::raw::c_void,
    data: *mut u8,
    len: usize,
    _timeout_ms: u32,
) -> usize {
    unsafe {
        let iohandle = iohandle as *const &dyn Uart;
        let uart: &dyn Uart = *iohandle;
        let data = std::slice::from_raw_parts_mut(data, len);
        match uart.read(data) {
            Ok(n) => n,
            Err(e) => {
                eprintln!("xmodem_read: {e:?}");
                0
            }
        }
    }
}

#[no_mangle]
extern "C" fn xmodem_write(iohandle: *mut std::os::raw::c_void, data: *const u8, len: usize) {
    unsafe {
        let iohandle = iohandle as *const &dyn Uart;
        let uart: &dyn Uart = *iohandle;
        let data = std::slice::from_raw_parts(data, len);
        match uart.write(data) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("xmodem_write: {e:?}");
            }
        }
    }
}
