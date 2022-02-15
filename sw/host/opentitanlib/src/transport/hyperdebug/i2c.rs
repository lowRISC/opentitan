// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cmp;
use std::rc::Rc;
use zerocopy::{AsBytes, FromBytes};

use crate::{bail, ensure};
use crate::io::i2c::{Bus, I2cError, Transfer};
use crate::transport::hyperdebug::{BulkInterface, Inner};
use crate::transport::{Result, TransportError};

pub struct HyperdebugI2cBus {
    inner: Rc<Inner>,
    interface: BulkInterface,
    bus_idx: u8,
    max_write_size: usize,
    max_read_size: usize,
}

const USB_MAX_SIZE: usize = 64;

/// Wire format of USB packet to request a short I2C transaction
/// (receiving at most 127 bytes).
#[derive(AsBytes, FromBytes, Debug)]
#[repr(C)]
struct CmdTransferShort {
    port: u8,
    addr: u8,
    write_count: u8,
    read_count: u8,
    data: [u8; USB_MAX_SIZE - 4],
}

/// Wire format of USB packet to request a long I2C transaction
/// (receiving up to 32767 bytes).
#[derive(AsBytes, FromBytes, Debug)]
#[repr(C)]
struct CmdTransferLong {
    port: u8,
    addr: u8,
    write_count: u8,
    read_count: u8,
    read_count1: u8,
    reserved: u8,
    data: [u8; USB_MAX_SIZE - 6],
}

/// Wire format of USB packet containing I2C transaction response.
#[derive(AsBytes, FromBytes, Debug)]
#[repr(C)]
struct RspTransfer {
    status_code: u16,
    reserved: u16,
    data: [u8; USB_MAX_SIZE - 4],
}
impl RspTransfer {
    fn new() -> Self {
        Self {
            status_code: 0,
            reserved: 0,
            data: [0; USB_MAX_SIZE - 4],
        }
    }
}

impl HyperdebugI2cBus {
    pub fn open(inner: &Rc<Inner>, i2c_interface: &BulkInterface, idx: u8) -> Result<Self> {
        let mut usb_handle = inner.usb_device.borrow_mut();

        // Exclusively claim I2C interface, preparing for bulk transfers.
        usb_handle.claim_interface(i2c_interface.interface)?;

        Ok(Self {
            inner: Rc::clone(&inner),
            interface: *i2c_interface,
            bus_idx: idx,
            max_read_size: 0x8000 as usize,
            max_write_size: 0x1000 as usize,
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
        let mut index = if rbuf.len() < 128 {
            // Short format header
            let mut req = CmdTransferShort {
                port: self.bus_idx | (((wbuf.len() & 0x0F00) >> 4) as u8),
                addr: addr,
                write_count: (wbuf.len() & 0x00FF) as u8,
                read_count: rbuf.len() as u8,
                data: [0; USB_MAX_SIZE - 4],
            };
            let databytes = cmp::min(USB_MAX_SIZE - 4, wbuf.len());
            req.data[..databytes].clone_from_slice(&wbuf[..databytes]);
            self.usb_write_bulk(&req.as_bytes()[..4 + databytes])?;
            databytes
        } else {
            // Long format header
            let mut req = CmdTransferLong {
                port: self.bus_idx | (((wbuf.len() & 0x0F00) >> 4) as u8),
                addr: addr,
                write_count: (wbuf.len() & 0x00FF) as u8,
                read_count: (rbuf.len() & 0x007F) as u8,
                read_count1: (rbuf.len() >> 7) as u8,
                reserved: 0,
                data: [0; USB_MAX_SIZE - 6],
            };
            let databytes = cmp::min(USB_MAX_SIZE - 6, wbuf.len());
            req.data[..databytes].clone_from_slice(&wbuf[..databytes]);
            self.usb_write_bulk(&req.as_bytes()[..6 + databytes])?;
            databytes
        };

        // Transmit any more data without further header.
        while index < wbuf.len() {
            let databytes = cmp::min(USB_MAX_SIZE, wbuf.len() - index);
            self.usb_write_bulk(&wbuf[index..index + databytes])?;
            index += databytes;
        }

        let mut resp = RspTransfer::new();
        let bytecount = self.usb_read_bulk(&mut resp.as_bytes_mut())?;
        ensure!(
            bytecount >= 4,
            TransportError::CommunicationError("Unrecognized response to I2C request".to_string())
        );
        match resp.status_code {
            0 => (),
            1 => bail!(I2cError::Timeout),
            2 => bail!(I2cError::Busy),
            n => bail!(TransportError::CommunicationError(format!("I2C error: {}", n))),
        }
        let databytes = bytecount - 4;
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
        Ok(self
            .inner
            .usb_device
            .borrow()
            .read_bulk(self.interface.in_endpoint, buf)?)
    }
}

impl Bus for HyperdebugI2cBus {
    fn run_transaction(&self, addr: u8, mut transaction: &mut [Transfer]) -> Result<()> {
        while transaction.len() > 0 {
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
}
