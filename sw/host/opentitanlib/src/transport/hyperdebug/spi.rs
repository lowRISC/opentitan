// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use rusb::{Direction, Recipient, RequestType};
use std::cell::Cell;
use std::mem::size_of;
use std::rc::Rc;
use zerocopy::{AsBytes, FromBytes};

use crate::io::spi::{
    AssertChipSelect, SpiError, Target, TargetChipDeassert, Transfer, TransferMode,
};
use crate::transport::hyperdebug::{BulkInterface, Inner};
use crate::transport::TransportError;

pub struct HyperdebugSpiTarget {
    inner: Rc<Inner>,
    interface: BulkInterface,
    target_idx: u8,
    max_chunk_size: usize,
    cs_asserted_count: Cell<u32>,
}

const USB_SPI_PKT_ID_CMD_GET_USB_SPI_CONFIG: u16 = 0;
const USB_SPI_PKT_ID_RSP_USB_SPI_CONFIG: u16 = 1;
const USB_SPI_PKT_ID_CMD_TRANSFER_START: u16 = 2;
const USB_SPI_PKT_ID_CMD_TRANSFER_CONTINUE: u16 = 3;
//const USB_SPI_PKT_ID_CMD_RESTART_RESPONSE: u16 = 4;
const USB_SPI_PKT_ID_RSP_TRANSFER_START: u16 = 5;
const USB_SPI_PKT_ID_RSP_TRANSFER_CONTINUE: u16 = 6;
const USB_SPI_PKT_ID_CMD_CHIP_SELECT: u16 = 7;
const USB_SPI_PKT_ID_RSP_CHIP_SELECT: u16 = 8;

//const USB_SPI_REQ_DISABLE: u8 = 1;
const USB_SPI_REQ_ENABLE: u8 = 0;

const USB_MAX_SIZE: usize = 64;
const FULL_DUPLEX: usize = 65535;

#[derive(AsBytes, FromBytes, Debug, Default)]
#[repr(C)]
struct RspUsbSpiConfig {
    packet_id: u16,
    max_write_chunk: u16,
    max_read_chunk: u16,
    feature_bitmap: u16,
}

#[derive(AsBytes, FromBytes, Debug)]
#[repr(C)]
struct CmdTransferStart {
    packet_id: u16,
    write_count: u16,
    read_count: u16,
    data: [u8; USB_MAX_SIZE - 6],
}
impl CmdTransferStart {
    fn new() -> Self {
        Self {
            packet_id: USB_SPI_PKT_ID_CMD_TRANSFER_START,
            write_count: 0,
            read_count: 0,
            data: [0; USB_MAX_SIZE - 6],
        }
    }
}

#[derive(AsBytes, FromBytes, Debug)]
#[repr(C)]
struct CmdTransferContinue {
    packet_id: u16,
    data_index: u16,
    data: [u8; USB_MAX_SIZE - 4],
}
impl CmdTransferContinue {
    fn new() -> Self {
        Self {
            packet_id: USB_SPI_PKT_ID_CMD_TRANSFER_CONTINUE,
            data_index: 0,
            data: [0; USB_MAX_SIZE - 4],
        }
    }
}

#[derive(AsBytes, FromBytes, Debug)]
#[repr(C)]
struct RspTransferStart {
    packet_id: u16,
    status_code: u16,
    data: [u8; USB_MAX_SIZE - 4],
}
impl RspTransferStart {
    fn new() -> Self {
        Self {
            packet_id: 0,
            status_code: 0,
            data: [0; USB_MAX_SIZE - 4],
        }
    }
}

#[derive(AsBytes, FromBytes, Debug)]
#[repr(C)]
struct RspTransferContinue {
    packet_id: u16,
    data_index: u16,
    data: [u8; USB_MAX_SIZE - 4],
}
impl RspTransferContinue {
    fn new() -> Self {
        Self {
            packet_id: 0,
            data_index: 0,
            data: [0; USB_MAX_SIZE - 4],
        }
    }
}

#[derive(AsBytes, FromBytes, Debug)]
#[repr(C)]
struct CmdChipSelect {
    packet_id: u16,
    flags: u16,
}
impl CmdChipSelect {
    fn new(assert_chip_select: bool) -> Self {
        Self {
            packet_id: USB_SPI_PKT_ID_CMD_CHIP_SELECT,
            flags: u16::from(assert_chip_select),
        }
    }
}

#[derive(AsBytes, FromBytes, Debug, Default)]
#[repr(C)]
struct RspChipSelect {
    packet_id: u16,
    status_code: u16,
}
impl RspChipSelect {
    fn new() -> Self {
        Self {
            packet_id: 0,
            status_code: 0,
        }
    }
}

impl HyperdebugSpiTarget {
    pub fn open(inner: &Rc<Inner>, spi_interface: &BulkInterface, idx: u8) -> Result<Self> {
        let mut usb_handle = inner.usb_device.borrow_mut();

        // Tell HyperDebug to enable SPI bridge, and to address particular SPI device.
        inner.selected_spi.set(idx);
        usb_handle.write_control(
            rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
            USB_SPI_REQ_ENABLE,
            idx as u16,
            spi_interface.interface as u16,
            &[],
        )?;

        // Exclusively claim SPI interface, preparing for bulk transfers.
        usb_handle.claim_interface(spi_interface.interface)?;

        // Initial bulk request/response to query capabilities.
        usb_handle.write_bulk(
            spi_interface.out_endpoint,
            &USB_SPI_PKT_ID_CMD_GET_USB_SPI_CONFIG.to_le_bytes(),
        )?;
        let mut resp: RspUsbSpiConfig = Default::default();
        let rc = usb_handle.read_bulk(spi_interface.in_endpoint, resp.as_bytes_mut())?;
        ensure!(
            rc == size_of::<RspUsbSpiConfig>(),
            TransportError::CommunicationError(
                "Unrecognized reponse to GET_USB_SPI_CONFIG".to_string()
            )
        );
        ensure!(
            resp.packet_id == USB_SPI_PKT_ID_RSP_USB_SPI_CONFIG,
            TransportError::CommunicationError(
                "Unrecognized reponse to GET_USB_SPI_CONFIG".to_string()
            )
        );
        // Verify that interface supports concurrent read/write.
        ensure!(
            (resp.feature_bitmap & 0x0001) != 0,
            TransportError::CommunicationError(
                "HyperDebug does not support bidirectional SPI".to_string()
            )
        );

        // Round the max chunk size down to the nearest power of two.
        let chunk =
            std::cmp::min(resp.max_write_chunk, resp.max_read_chunk).next_power_of_two() / 2;
        Ok(Self {
            inner: Rc::clone(inner),
            interface: *spi_interface,
            target_idx: idx,
            max_chunk_size: chunk as usize,
            cs_asserted_count: Cell::new(0),
        })
    }

    /// Instruct HyperDebug device which SPI bus subsequent transactions should be forwarded to.
    fn select_my_spi_bus(&self) -> Result<()> {
        if self.inner.selected_spi.get() != self.target_idx {
            self.inner.selected_spi.set(self.target_idx);
            self.inner.usb_device.borrow().write_control(
                rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
                USB_SPI_REQ_ENABLE,
                self.target_idx as u16,
                self.interface.interface as u16,
                &[],
            )?;
        }
        Ok(())
    }

    /// Transmit data for a single SPI operation, using one or more USB packets.
    fn transmit(&self, wbuf: &[u8], rbuf_len: usize) -> Result<()> {
        let mut req = CmdTransferStart::new();
        req.write_count = wbuf.len() as u16;
        req.read_count = rbuf_len as u16;
        let databytes = std::cmp::min(USB_MAX_SIZE - 6, wbuf.len());
        req.data[0..databytes].clone_from_slice(&wbuf[0..databytes]);
        self.usb_write_bulk(&req.as_bytes()[0..6 + databytes])?;
        let mut index = databytes;

        while index < wbuf.len() {
            let mut req = CmdTransferContinue::new();
            req.data_index = index as u16;
            let databytes = std::cmp::min(USB_MAX_SIZE - 4, wbuf.len() - index);
            req.data[0..databytes].clone_from_slice(&wbuf[index..index + databytes]);
            self.usb_write_bulk(&req.as_bytes()[0..4 + databytes])?;
            index += databytes;
        }
        Ok(())
    }

    /// Receive data for a single SPI operation, using one or more USB packets.
    fn receive(&self, rbuf: &mut [u8]) -> Result<()> {
        let mut resp = RspTransferStart::new();
        let bytecount = self.usb_read_bulk(resp.as_bytes_mut())?;
        ensure!(
            bytecount >= 4,
            TransportError::CommunicationError(
                "Unrecognized reponse to TRANSFER_START".to_string()
            )
        );
        ensure!(
            resp.packet_id == USB_SPI_PKT_ID_RSP_TRANSFER_START,
            TransportError::CommunicationError(
                "Unrecognized reponse to TRANSFER_START".to_string()
            )
        );
        ensure!(
            resp.status_code == 0,
            TransportError::CommunicationError(format!("SPI error ({})", resp.status_code))
        );
        let databytes = bytecount - 4;
        rbuf[0..databytes].clone_from_slice(&resp.data[0..databytes]);
        let mut index = databytes;
        while index < rbuf.len() {
            let mut resp = RspTransferContinue::new();
            let bytecount = self.usb_read_bulk(resp.as_bytes_mut())?;
            ensure!(
                bytecount > 4,
                TransportError::CommunicationError(
                    "Unrecognized reponse to TRANSFER_START".to_string()
                )
            );
            ensure!(
                resp.packet_id == USB_SPI_PKT_ID_RSP_TRANSFER_CONTINUE,
                TransportError::CommunicationError(
                    "Unrecognized reponse to TRANSFER_START".to_string()
                )
            );
            ensure!(
                resp.data_index == index as u16,
                TransportError::CommunicationError(
                    "Unexpected byte index in reponse to TRANSFER_START".to_string()
                )
            );
            let databytes = bytecount - 4;
            rbuf[index..index + databytes].clone_from_slice(&resp.data[0..databytes]);
            index += databytes;
        }
        Ok(())
    }

    /// Request assertion or deassertion of chip select
    fn do_assert_cs(&self, assert: bool) -> Result<()> {
        let mut count = self.cs_asserted_count.get();
        if assert {
            if count == 0 {
                self._do_assert_cs(assert)?;
            }
            count += 1;
        } else {
            if count == 1 {
                self._do_assert_cs(assert)?;
            }
            count -= 1;
        }
        self.cs_asserted_count.set(count);
        Ok(())
    }

    fn _do_assert_cs(&self, assert: bool) -> Result<()> {
        let req = CmdChipSelect::new(assert);
        self.usb_write_bulk(req.as_bytes())?;

        let mut resp = RspChipSelect::new();
        let bytecount = self.usb_read_bulk(resp.as_bytes_mut())?;
        ensure!(
            bytecount >= 4,
            TransportError::CommunicationError("Unrecognized reponse to CHIP_SELECT".to_string())
        );
        ensure!(
            resp.packet_id == USB_SPI_PKT_ID_RSP_CHIP_SELECT,
            TransportError::CommunicationError("Unrecognized reponse to CHIP_SELECT".to_string())
        );
        ensure!(
            resp.status_code == 0,
            TransportError::CommunicationError("SPI error".to_string())
        );
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
}

impl Target for HyperdebugSpiTarget {
    fn get_transfer_mode(&self) -> Result<TransferMode> {
        Ok(TransferMode::Mode0)
    }
    fn set_transfer_mode(&self, _mode: TransferMode) -> Result<()> {
        todo!();
    }

    fn get_bits_per_word(&self) -> Result<u32> {
        Ok(8)
    }
    fn set_bits_per_word(&self, bits_per_word: u32) -> Result<()> {
        match bits_per_word {
            8 => Ok(()),
            _ => Err(SpiError::InvalidWordSize(bits_per_word).into()),
        }
    }

    fn get_max_speed(&self) -> Result<u32> {
        let mut buf = String::new();
        let captures = self.inner.cmd_one_line_output_match(
            &format!("spiget {}", &self.target_idx),
            &super::SPI_REGEX,
            &mut buf,
        )?;
        Ok(captures.get(3).unwrap().as_str().parse().unwrap())
    }
    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        self.inner
            .cmd_no_output(&format!("spisetspeed {} {}", &self.target_idx, frequency))
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        // The protocol imposes no limits to the number of Transfers
        // in a transaction.
        Ok(usize::MAX)
    }

    fn max_chunk_size(&self) -> Result<usize> {
        Ok(self.max_chunk_size)
    }

    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        let mut idx: usize = 0;
        self.select_my_spi_bus()?;
        self.do_assert_cs(true)?;
        while idx < transaction.len() {
            match &mut transaction[idx..] {
                [Transfer::Write(wbuf), Transfer::Read(rbuf), ..] => {
                    // Hyperdebug can do SPI write followed by SPI read as a single USB
                    // request/reply.  Take advantage of that by detecting pairs of
                    // Transfer::Write followed by Transfer::Read.
                    ensure!(
                        wbuf.len() <= self.max_chunk_size,
                        SpiError::InvalidDataLength(wbuf.len())
                    );
                    ensure!(
                        rbuf.len() <= self.max_chunk_size,
                        SpiError::InvalidDataLength(rbuf.len())
                    );
                    self.transmit(wbuf, rbuf.len())?;
                    self.receive(rbuf)?;
                    // Skip two steps ahead, as two items were processed.
                    idx += 2;
                    continue;
                }
                [Transfer::Write(wbuf), ..] => {
                    ensure!(
                        wbuf.len() <= self.max_chunk_size,
                        SpiError::InvalidDataLength(wbuf.len())
                    );
                    self.transmit(wbuf, 0)?;
                    self.receive(&mut [])?;
                }
                [Transfer::Read(rbuf), ..] => {
                    ensure!(
                        rbuf.len() <= self.max_chunk_size,
                        SpiError::InvalidDataLength(rbuf.len())
                    );
                    self.transmit(&[], rbuf.len())?;
                    self.receive(rbuf)?;
                }
                [Transfer::Both(wbuf, rbuf), ..] => {
                    ensure!(
                        rbuf.len() == wbuf.len(),
                        SpiError::MismatchedDataLength(wbuf.len(), rbuf.len())
                    );
                    ensure!(
                        wbuf.len() <= self.max_chunk_size,
                        SpiError::InvalidDataLength(wbuf.len())
                    );
                    self.transmit(wbuf, FULL_DUPLEX)?;
                    self.receive(rbuf)?;
                }
                [] => (),
            }
            idx += 1;
        }
        self.do_assert_cs(false)?;
        Ok(())
    }

    fn assert_cs(self: Rc<Self>) -> Result<AssertChipSelect> {
        self.do_assert_cs(true)?;
        Ok(AssertChipSelect::new(self))
    }
}

impl TargetChipDeassert for HyperdebugSpiTarget {
    fn deassert_cs(&self) {
        // We cannot propagate errors through `Drop::drop()`, so panic on any error.  (Logging
        // would be another option.)
        self.do_assert_cs(false)
            .expect("Error while deasserting CS");
    }
}
