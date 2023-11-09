// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use std::cell::Cell;
use std::cmp;
use std::rc::Rc;
use std::time::Duration;
use zerocopy::{AsBytes, FromBytes, FromZeroes};

use crate::io::i2c::{self, Bus, DeviceStatus, DeviceTransfer, I2cError, ReadStatus, Transfer};
use crate::transport::hyperdebug::{BulkInterface, Inner};
use crate::transport::{TransportError, TransportInterfaceType};

pub struct HyperdebugI2cBus {
    inner: Rc<Inner>,
    interface: BulkInterface,
    cmsis_encapsulation: bool,
    bus_idx: u8,
    mode: Cell<Mode>,
    max_write_size: usize,
    max_read_size: usize,
    default_addr: Cell<Option<u8>>,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Mode {
    Host,
    Device,
}

const USB_MAX_SIZE: usize = 64;

/// Wire format of USB packet to request a short I2C transaction
/// (receiving at most 127 bytes).
#[derive(AsBytes, FromBytes, FromZeroes, Debug)]
#[allow(dead_code)] // Fields not explicitly read anywhere
#[repr(packed)]
struct CmdTransferShort {
    encapsulation_header: u8,
    port: u8,
    addr: u8,
    write_count: u8,
    read_count: u8,
    data: [u8; USB_MAX_SIZE - 4],
}

/// Wire format of USB packet to request a long I2C transaction
/// (receiving up to 32767 bytes).
#[derive(AsBytes, FromBytes, FromZeroes, Debug)]
#[allow(dead_code)] // Fields not explicitly read anywhere
#[repr(packed)]
struct CmdTransferLong {
    encapsulation_header: u8,
    port: u8,
    addr: u8,
    write_count: u8,
    read_count: u8,
    read_count1: u8,
    reserved: u8,
    data: [u8; USB_MAX_SIZE - 6],
}

/// Wire format of USB packet containing I2C transaction response.
#[derive(AsBytes, FromBytes, FromZeroes, Debug)]
#[allow(dead_code)] // Reserved field not read anywhere
#[repr(packed)]
struct RspTransfer {
    encapsulation_header: u8,
    status_code: u16,
    reserved: u16,
    data: [u8; USB_MAX_SIZE],
}
impl RspTransfer {
    fn new() -> Self {
        Self {
            encapsulation_header: 0,
            status_code: 0,
            reserved: 0,
            data: [0; USB_MAX_SIZE],
        }
    }
}

#[derive(AsBytes, FromBytes, FromZeroes, Debug)]
#[allow(dead_code)] // Fields not explicitly read anywhere
#[repr(packed)]
struct CmdGetDeviceStatus {
    encapsulation_header: u8,
    port: u8,
    device_cmd: u8,
    timeout_ms: u16,
}

// Values for use in `CmdGetDeviceStatus.device_cmd`.
const I2C_DEVICE_CMD_GET_DEVICE_STATUS: u8 = 0x00;
const I2C_DEVICE_CMD_PREPARE_READ_DATA: u8 = 0x01;

// Bits for use in upper half of `CmdGetDeviceStatus.port`.
const I2C_DEVICE_FLAG_STICKY: u8 = 0x80;

#[derive(AsBytes, FromBytes, FromZeroes, Debug)]
#[repr(packed)]
struct RspGetDeviceStatus {
    encapsulation_header: u8,
    struct_size: u16,
    read_status: u8,
    blocked_read_addr: u8,
    transcript_size: u16,
    data: [u8; USB_MAX_SIZE],
}
impl RspGetDeviceStatus {
    fn new() -> Self {
        Self {
            encapsulation_header: 0,
            struct_size: 0,
            read_status: 0,
            blocked_read_addr: 0,
            transcript_size: 0,
            data: [0u8; USB_MAX_SIZE],
        }
    }
}

#[derive(AsBytes, FromBytes, FromZeroes, Debug)]
#[allow(dead_code)] // Fields not explicitly read anywhere
#[repr(packed)]
struct CmdPrepareReadData {
    encapsulation_header: u8,
    port: u8,
    device_cmd: u8,
    data_size: u16,
    data: [u8; USB_MAX_SIZE - 4],
}

impl HyperdebugI2cBus {
    /// If `cmsis_encapsulation` is set to true, then every request on the USB bus will have an
    /// extra byte "in front" containing this value.  Correspondingly, every response is expected
    /// to carry this same value as the first byte.
    const CMSIS_DAP_CUSTOM_COMMAND_I2C: u8 = 0x81;

    /// Alternative command only available when protocol encapsulated in CMSIS.
    const CMSIS_DAP_CUSTOM_COMMAND_I2C_DEVICE: u8 = 0x82;

    pub fn open(
        inner: &Rc<Inner>,
        i2c_interface: &BulkInterface,
        cmsis_encapsulation: bool,
        idx: u8,
        mode: Mode,
    ) -> Result<Self> {
        ensure!(
            idx < 16,
            TransportError::InvalidInstance(TransportInterfaceType::I2c, idx.to_string())
        );
        let mut usb_handle = inner.usb_device.borrow_mut();

        // Exclusively claim I2C interface, preparing for bulk transfers.
        usb_handle.claim_interface(i2c_interface.interface)?;

        Ok(Self {
            inner: Rc::clone(inner),
            interface: *i2c_interface,
            cmsis_encapsulation,
            bus_idx: idx,
            mode: Cell::new(mode),
            max_read_size: 0x8000,
            max_write_size: 0x1000,
            default_addr: Cell::new(None),
        })
    }

    /// Transmit data for a single I2C operation, using one or more USB packets.
    fn transmit_then_receive(&self, addr: u8, wbuf: &[u8], rbuf: &mut [u8]) -> Result<()> {
        ensure!(
            rbuf.len() < self.max_read_size,
            I2cError::InvalidDataLength(rbuf.len())
        );
        ensure!(
            wbuf.len() < self.max_write_size,
            I2cError::InvalidDataLength(wbuf.len())
        );
        let encapsulation_header_size = if self.cmsis_encapsulation { 1 } else { 0 };
        let mut index = if rbuf.len() < 128 {
            // Short format header
            let mut req = CmdTransferShort {
                encapsulation_header: Self::CMSIS_DAP_CUSTOM_COMMAND_I2C,
                port: self.bus_idx | (((wbuf.len() & 0x0F00) >> 4) as u8),
                addr,
                write_count: (wbuf.len() & 0x00FF) as u8,
                read_count: rbuf.len() as u8,
                data: [0; USB_MAX_SIZE - 4],
            };
            let databytes = cmp::min(USB_MAX_SIZE - 4 - encapsulation_header_size, wbuf.len());
            req.data[..databytes].clone_from_slice(&wbuf[..databytes]);
            self.usb_write_bulk(&req.as_bytes()[1 - encapsulation_header_size..1 + 4 + databytes])?;
            databytes
        } else {
            // Long format header
            let mut req = CmdTransferLong {
                encapsulation_header: Self::CMSIS_DAP_CUSTOM_COMMAND_I2C,
                port: self.bus_idx | (((wbuf.len() & 0x0F00) >> 4) as u8),
                addr,
                write_count: (wbuf.len() & 0x00FF) as u8,
                read_count: (rbuf.len() & 0x007F) as u8,
                read_count1: (rbuf.len() >> 7) as u8,
                reserved: 0,
                data: [0; USB_MAX_SIZE - 6],
            };
            let databytes = cmp::min(USB_MAX_SIZE - 6 - encapsulation_header_size, wbuf.len());
            req.data[..databytes].clone_from_slice(&wbuf[..databytes]);
            self.usb_write_bulk(&req.as_bytes()[1 - encapsulation_header_size..1 + 6 + databytes])?;
            databytes
        };

        // Transmit any more data without further header.
        while index < wbuf.len() {
            let databytes = cmp::min(USB_MAX_SIZE, wbuf.len() - index);
            self.usb_write_bulk(&wbuf[index..index + databytes])?;
            index += databytes;
        }

        let mut resp = RspTransfer::new();
        let mut bytecount = 0;
        while bytecount < 4 + encapsulation_header_size {
            let read_count = self.usb_read_bulk(
                &mut resp.as_bytes_mut()[1 - encapsulation_header_size + bytecount..][..64],
            )?;
            ensure!(
                read_count > 0,
                TransportError::CommunicationError("Truncated I2C response".to_string())
            );
            bytecount += read_count;
        }
        if encapsulation_header_size == 1 {
            ensure!(
                resp.encapsulation_header == Self::CMSIS_DAP_CUSTOM_COMMAND_I2C,
                TransportError::CommunicationError(
                    "Unrecognized CMSIS-DAP response to I2C request".to_string()
                )
            );
        }
        match resp.status_code {
            0 => (),
            1 => bail!(I2cError::Timeout),
            2 => bail!(I2cError::Busy),
            n => bail!(TransportError::CommunicationError(format!(
                "I2C error: {}",
                n
            ))),
        }
        let databytes = bytecount - 4 - encapsulation_header_size;
        rbuf[..databytes].clone_from_slice(&resp.data[..databytes]);
        let mut index = databytes;
        while index < rbuf.len() {
            let databytes = self.usb_read_bulk(&mut resp.data[index..])?;
            ensure!(
                databytes > 0,
                TransportError::CommunicationError(
                    "Unrecognized reponse to I2C request".to_string()
                )
            );
            index += databytes;
        }
        Ok(())
    }

    /// Send one USB packet.
    fn usb_write_bulk(&self, buf: &[u8]) -> Result<()> {
        self.inner
            .usb_device
            .borrow()
            .write_bulk(self.interface.out_endpoint, buf)?;
        Ok(())
    }

    /// Receive one USB packet.
    fn usb_read_bulk(&self, buf: &mut [u8]) -> Result<usize> {
        self.inner
            .usb_device
            .borrow()
            .read_bulk(self.interface.in_endpoint, buf)
    }

    /// Receive one USB packet with non-default timeout.
    fn usb_read_bulk_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        self.inner
            .usb_device
            .borrow()
            .read_bulk_timeout(self.interface.in_endpoint, buf, timeout)
    }
}

impl Bus for HyperdebugI2cBus {
    fn set_mode(&self, mode: i2c::Mode) -> Result<()> {
        match mode {
            // Put I2C debugger into host mode (this is the default).
            i2c::Mode::Host => {
                self.inner
                    .cmd_no_output(&format!("i2c set mode {} host", &self.bus_idx))?;
                self.mode.set(Mode::Host);
            }
            // Put I2C debugger into device mode.
            i2c::Mode::Device(addr) => {
                self.inner
                    .cmd_no_output(&format!("i2c set mode {} device {}", &self.bus_idx, addr))?;
                self.mode.set(Mode::Device);
            }
        }
        Ok(())
    }

    /// Gets the maximum allowed speed of the I2C bus.
    fn get_max_speed(&self) -> Result<u32> {
        let mut buf = String::new();
        let captures = self.inner.cmd_one_line_output_match(
            &format!("i2c info {}", &self.bus_idx),
            &super::SPI_REGEX,
            &mut buf,
        )?;
        Ok(captures.get(3).unwrap().as_str().parse().unwrap())
    }

    /// Sets the maximum allowed speed of the I2C bus, typical values are 100_000, 400_000 or
    /// 1_000_000.
    fn set_max_speed(&self, max_speed: u32) -> Result<()> {
        self.inner
            .cmd_no_output(&format!("i2c set speed {} {}", &self.bus_idx, max_speed))
    }

    fn set_default_address(&self, addr: u8) -> Result<()> {
        self.default_addr.set(Some(addr));
        Ok(())
    }

    fn run_transaction(&self, addr: Option<u8>, mut transaction: &mut [Transfer]) -> Result<()> {
        let addr = addr
            .or(self.default_addr.get())
            .ok_or(I2cError::MissingAddress)?;
        while !transaction.is_empty() {
            match transaction {
                [Transfer::Write(wbuf), Transfer::Read(rbuf), ..] => {
                    // Hyperdebug can do I2C write followed by I2C read as a single USB
                    // request/reply.  Take advantage of that by detecting pairs of
                    // Transfer::Write followed by Transfer::Read.
                    ensure!(
                        wbuf.len() <= self.max_write_size,
                        I2cError::InvalidDataLength(wbuf.len())
                    );
                    ensure!(
                        rbuf.len() <= self.max_read_size,
                        I2cError::InvalidDataLength(rbuf.len())
                    );
                    self.transmit_then_receive(addr, wbuf, rbuf)?;
                    // Skip two steps ahead, as two items were processed.
                    transaction = &mut transaction[2..];
                }
                [Transfer::Write(wbuf), ..] => {
                    ensure!(
                        wbuf.len() <= self.max_write_size,
                        I2cError::InvalidDataLength(wbuf.len())
                    );
                    self.transmit_then_receive(addr, wbuf, &mut [])?;
                    transaction = &mut transaction[1..];
                }
                [Transfer::Read(rbuf), ..] => {
                    ensure!(
                        rbuf.len() <= self.max_read_size,
                        I2cError::InvalidDataLength(rbuf.len())
                    );
                    self.transmit_then_receive(addr, &[], rbuf)?;
                    transaction = &mut transaction[1..];
                }
                [] => (),
            }
        }
        Ok(())
    }

    fn get_device_status(&self, timeout: Duration) -> Result<DeviceStatus> {
        ensure!(
            self.cmsis_encapsulation,
            TransportError::UnsupportedOperation
        );
        ensure!(self.mode.get() == Mode::Device, I2cError::NotInDeviceMode);
        let timeout_ms = timeout.as_millis();
        let req = CmdGetDeviceStatus {
            encapsulation_header: Self::CMSIS_DAP_CUSTOM_COMMAND_I2C_DEVICE,
            port: self.bus_idx,
            device_cmd: I2C_DEVICE_CMD_GET_DEVICE_STATUS,
            timeout_ms: if timeout_ms > 65535 {
                65535
            } else {
                timeout_ms as u16
            },
        };
        self.usb_write_bulk(req.as_bytes())?;

        let mut resp = RspGetDeviceStatus::new();
        let mut bytecount = 0;
        while bytecount < 7 {
            let read_count = self.usb_read_bulk_timeout(
                &mut resp.as_bytes_mut()[bytecount..][..64],
                Duration::from_millis(req.timeout_ms as u64 + 500),
            )?;
            ensure!(
                read_count > 0,
                TransportError::CommunicationError("Truncated I2C response".to_string())
            );
            bytecount += read_count;
        }
        ensure!(
            resp.encapsulation_header == Self::CMSIS_DAP_CUSTOM_COMMAND_I2C_DEVICE,
            TransportError::CommunicationError(
                "Unrecognized CMSIS-DAP response to I2C request".to_string()
            )
        );
        let skip_bytes = resp.struct_size - 6;

        let mut databytes: Vec<u8> = Vec::new();
        databytes.extend_from_slice(&resp.data[..bytecount - 7]);

        while databytes.len() < (skip_bytes + resp.transcript_size) as usize {
            let original_length = databytes.len();
            databytes.resize(original_length + 64, 0u8);
            let c = self.usb_read_bulk(&mut databytes[original_length..])?;
            databytes.resize(original_length + c, 0u8);
        }

        let mut transfers = Vec::new();
        let mut idx = skip_bytes as usize;
        while idx < databytes.len() {
            let addr = databytes[idx] >> 1;
            let is_read = (databytes[idx] & 0x01) != 0;
            let timeout = (databytes[idx + 1] & 0x01) != 0;
            let transfer_len = databytes[idx + 2] as usize + ((databytes[idx + 3] as usize) << 8);
            idx += 4;
            if is_read {
                // Read transfer
                transfers.push(DeviceTransfer::Read {
                    addr,
                    timeout,
                    len: transfer_len,
                });
            } else {
                // Write transfer
                transfers.push(DeviceTransfer::Write {
                    addr,
                    data: databytes[idx..idx + transfer_len].to_vec(),
                });
                idx += (transfer_len + 3) & !3;
            }
        }

        let read_status = match resp.read_status {
            0 => ReadStatus::Idle,
            1 => ReadStatus::DataPrepared,
            2 => ReadStatus::WaitingForData(resp.blocked_read_addr >> 1),
            _ => bail!(TransportError::CommunicationError(
                "Unrecognized I2C read status".to_string()
            )),
        };

        Ok(DeviceStatus {
            transfers,
            read_status,
        })
    }

    fn prepare_read_data(&self, data: &[u8], sticky: bool) -> Result<()> {
        ensure!(
            self.cmsis_encapsulation,
            TransportError::UnsupportedOperation
        );
        ensure!(self.mode.get() == Mode::Device, I2cError::NotInDeviceMode);
        if data.len() > 256 {
            bail!(TransportError::CommunicationError(
                "Data exceeds maximum length".to_string()
            ))
        }
        let flags = if sticky { I2C_DEVICE_FLAG_STICKY } else { 0 };
        let mut req = CmdPrepareReadData {
            encapsulation_header: Self::CMSIS_DAP_CUSTOM_COMMAND_I2C_DEVICE,
            port: self.bus_idx | flags,
            device_cmd: I2C_DEVICE_CMD_PREPARE_READ_DATA,
            data_size: data.len() as u16,
            data: [0; USB_MAX_SIZE - 4],
        };
        // Compute how many data bytes fit in the first USB packet after the header.
        let mut index = std::cmp::min(64 - 5, data.len());
        req.data[..index].clone_from_slice(&data[..index]);
        self.usb_write_bulk(&req.as_bytes()[..5 + index])?;

        while index < data.len() {
            let packet_len = std::cmp::min(64, data.len() - index);
            self.usb_write_bulk(&data[index..index + packet_len])?;
            index += packet_len;
        }

        let mut resp = 0u8;
        let c = self.usb_read_bulk(std::slice::from_mut(&mut resp))?;
        ensure!(
            c == 1 && resp == Self::CMSIS_DAP_CUSTOM_COMMAND_I2C_DEVICE,
            TransportError::CommunicationError(
                "Unrecognized CMSIS-DAP response to I2C request".to_string()
            )
        );
        Ok(())
    }
}
