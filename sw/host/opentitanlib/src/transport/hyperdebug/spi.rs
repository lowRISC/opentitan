// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use rusb::{Direction, Recipient, RequestType};
use std::cell::Cell;
use std::mem::size_of;
use std::rc::Rc;
use zerocopy::{AsBytes, FromBytes};

use crate::io::eeprom;
use crate::io::spi::{
    AssertChipSelect, MaxSizes, SpiError, Target, TargetChipDeassert, Transfer, TransferMode,
};
use crate::transport::hyperdebug::{BulkInterface, Inner};
use crate::transport::TransportError;

pub struct HyperdebugSpiTarget {
    inner: Rc<Inner>,
    interface: BulkInterface,
    target_enable_cmd: u8,
    target_idx: u8,
    feature_bitmap: u16,
    max_sizes: MaxSizes,
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
const USB_SPI_PKT_ID_CMD_EEPROM_TRANSFER_START: u16 = 9;

pub const USB_SPI_REQ_ENABLE: u8 = 0;
//const USB_SPI_REQ_DISABLE: u8 = 1;
pub const USB_SPI_REQ_ENABLE_AP: u8 = 2;
pub const USB_SPI_REQ_ENABLE_EC: u8 = 3;

const USB_MAX_SIZE: usize = 64;
const FULL_DUPLEX: usize = 65535;

const FEATURE_BIT_FULL_DUPLEX: u16 = 0x0001;
const FEATURE_BIT_EEPROM: u16 = 0x0002;
const FEATURE_BIT_EEPROM_DUAL: u16 = 0x0004;
const FEATURE_BIT_EEPROM_QUAD: u16 = 0x0008;
const FEATURE_BIT_EEPROM_OCTO: u16 = 0x0010;
const FEATURE_BIT_EEPROM_DTR: u16 = 0x0020;
const FEATURE_BIT_EEPROM_DOUBLE_BUFFER: u16 = 0x0040;

const EEPROM_FLAGS_OPCODE_LEN_POS: u8 = 0;
const EEPROM_FLAGS_ADDR_LEN_POS: u8 = 2;
const EEPROM_FLAGS_MODE_111: u32 = 0x00000000;
const EEPROM_FLAGS_MODE_11N: u32 = 0x00000020;
const EEPROM_FLAGS_MODE_1NN: u32 = 0x00000040;
const EEPROM_FLAGS_MODE_NNN: u32 = 0x00000060;
const EEPROM_FLAGS_WIDTH_1WIRE: u32 = 0x00000000;
const EEPROM_FLAGS_WIDTH_2WIRE: u32 = 0x00000080;
const EEPROM_FLAGS_WIDTH_4WIRE: u32 = 0x00000100;
const EEPROM_FLAGS_WIDTH_8WIRE: u32 = 0x00000180;
const EEPROM_FLAGS_DTR: u32 = 0x00000200;
const EEPROM_FLAGS_DUMMY_CYCLES_POS: u8 = 10;
const EEPROM_FLAGS_WRITE_ENABLE: u32 = 0x10000000;
const EEPROM_FLAGS_POLL_BUSY: u32 = 0x20000000;
const EEPROM_FLAGS_DOUBLE_BUFFER: u32 = 0x40000000;
const EEPROM_FLAGS_WRITE: u32 = 0x80000000;

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
struct CmdEepromTransferStart {
    packet_id: u16,
    count: u16,
    flags: u32,
    data: [u8; USB_MAX_SIZE - 8],
}
impl CmdEepromTransferStart {
    fn new() -> Self {
        Self {
            packet_id: USB_SPI_PKT_ID_CMD_EEPROM_TRANSFER_START,
            count: 0,
            flags: 0,
            data: [0; USB_MAX_SIZE - 8],
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

enum StreamState<'a> {
    NoPending,
    PendingWrite,
    PendingRead(&'a mut [u8]),
}

impl HyperdebugSpiTarget {
    pub fn open(
        inner: &Rc<Inner>,
        spi_interface: &BulkInterface,
        enable_cmd: u8,
        idx: u8,
    ) -> Result<Self> {
        let mut usb_handle = inner.usb_device.borrow_mut();

        // Tell HyperDebug to enable SPI bridge, and to address particular SPI device.
        inner.selected_spi.set(idx);
        usb_handle.write_control(
            rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
            enable_cmd,
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
            (resp.feature_bitmap & FEATURE_BIT_FULL_DUPLEX) != 0,
            TransportError::CommunicationError(
                "HyperDebug does not support bidirectional SPI".to_string()
            )
        );

        log::info!("HyperDebug feature bitmap: 0x{:04x}", resp.feature_bitmap);

        Ok(Self {
            inner: Rc::clone(inner),
            interface: *spi_interface,
            target_enable_cmd: enable_cmd,
            target_idx: idx,
            feature_bitmap: resp.feature_bitmap,
            max_sizes: MaxSizes {
                read: resp.max_read_chunk as usize,
                write: resp.max_write_chunk as usize,
            },
            cs_asserted_count: Cell::new(0),
        })
    }

    /// Instruct HyperDebug device which SPI bus subsequent transactions should be forwarded to.
    fn select_my_spi_bus(&self) -> Result<()> {
        if self.inner.selected_spi.get() != self.target_idx {
            self.inner.selected_spi.set(self.target_idx);
            self.inner.usb_device.borrow().write_control(
                rusb::request_type(Direction::Out, RequestType::Vendor, Recipient::Interface),
                self.target_enable_cmd,
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
            TransportError::CommunicationError("Short reponse to TRANSFER_START".to_string())
        );
        ensure!(
            resp.packet_id == USB_SPI_PKT_ID_RSP_TRANSFER_START,
            TransportError::CommunicationError(format!(
                "Unrecognized reponse to TRANSFER_START: {}",
                resp.packet_id
            ))
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
                    "Short reponse to TRANSFER_CONTINUE".to_string()
                )
            );
            ensure!(
                resp.packet_id == USB_SPI_PKT_ID_RSP_TRANSFER_CONTINUE,
                TransportError::CommunicationError(format!(
                    "Unrecognized reponse to TRANSFER_CONTINUE: {}",
                    resp.packet_id
                ))
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

    fn receive_first_streaming(&self) -> Result<()> {
        let mut resp = RspTransferStart::new();
        let bytecount = self.usb_read_bulk(resp.as_bytes_mut())?;
        ensure!(
            bytecount >= 4,
            TransportError::CommunicationError("Short reponse to TRANSFER_START".to_string())
        );
        ensure!(
            resp.packet_id == USB_SPI_PKT_ID_RSP_TRANSFER_START,
            TransportError::CommunicationError(format!(
                "Unrecognized reponse to TRANSFER_START: {}",
                resp.packet_id
            ))
        );
        ensure!(
            resp.status_code == 0x0B,
            TransportError::CommunicationError(format!(
                "SPI error ({}), expected streaming response",
                resp.status_code
            ))
        );
        Ok(())
    }

    fn verify_width(&self, requested_width: eeprom::DataWidth) -> Result<()> {
        match requested_width {
            eeprom::DataWidth::Single => (),
            eeprom::DataWidth::Dual => ensure!(
                self.feature_bitmap & FEATURE_BIT_EEPROM_DUAL != 0,
                SpiError::InvalidDataWidth(requested_width)
            ),
            eeprom::DataWidth::Quad => ensure!(
                self.feature_bitmap & FEATURE_BIT_EEPROM_QUAD != 0,
                SpiError::InvalidDataWidth(requested_width)
            ),
            eeprom::DataWidth::Octo => ensure!(
                self.feature_bitmap & FEATURE_BIT_EEPROM_OCTO != 0,
                SpiError::InvalidDataWidth(requested_width)
            ),
        }
        Ok(())
    }

    /// Transmit data for a single SPI operation, using one or more USB packets.
    fn eeprom_transmit<'a>(
        &self,
        write_enable: Option<&eeprom::Cmd>,
        cmd: &eeprom::Cmd,
        wbuf: &[u8],
        rbuf: &'a mut [u8],
        wait_for_busy_clear: bool,
        stream_state: StreamState,
    ) -> Result<StreamState<'a>> {
        let double_buffer = self.feature_bitmap & FEATURE_BIT_EEPROM_DOUBLE_BUFFER != 0;

        self.verify_width(cmd.get_width())?;

        let mut req = CmdEepromTransferStart::new();
        let mut idx = 0;
        if rbuf.is_empty() {
            req.flags |= EEPROM_FLAGS_WRITE;
            req.count = wbuf.len() as u16;
        } else {
            req.count = rbuf.len() as u16;
        }

        req.flags |= match cmd.get_switch() {
            eeprom::Switch::Mode111 => EEPROM_FLAGS_MODE_111,
            eeprom::Switch::Mode11N => EEPROM_FLAGS_MODE_11N,
            eeprom::Switch::Mode1NN => EEPROM_FLAGS_MODE_1NN,
            eeprom::Switch::ModeNNN => EEPROM_FLAGS_MODE_NNN,
        };
        req.flags |= match cmd.get_width() {
            eeprom::DataWidth::Single => EEPROM_FLAGS_WIDTH_1WIRE,
            eeprom::DataWidth::Dual => EEPROM_FLAGS_WIDTH_2WIRE,
            eeprom::DataWidth::Quad => EEPROM_FLAGS_WIDTH_4WIRE,
            eeprom::DataWidth::Octo => EEPROM_FLAGS_WIDTH_8WIRE,
        };
        if cmd.get_double_transfer_rate() {
            ensure!(
                self.feature_bitmap & FEATURE_BIT_EEPROM_DTR != 0,
                SpiError::InvalidDoubleTransferRate()
            );
            req.flags |= EEPROM_FLAGS_DTR;
        }

        // Command bytes
        req.flags |= (cmd.get_opcode_len() as u32) << EEPROM_FLAGS_OPCODE_LEN_POS;

        if double_buffer {
            req.flags |= EEPROM_FLAGS_DOUBLE_BUFFER;
        }
        if let Some(pre_cmd) = write_enable {
            req.flags |= EEPROM_FLAGS_WRITE_ENABLE;
            let opcode_bytes = pre_cmd.get_opcode();
            if opcode_bytes.len() != 1 {
                panic!("Illegal write enable sequence");
            }
            req.data[idx..idx + opcode_bytes.len()].clone_from_slice(opcode_bytes);
            idx += opcode_bytes.len();
        }
        if wait_for_busy_clear {
            req.flags |= EEPROM_FLAGS_POLL_BUSY;
        }
        let opcode_bytes = cmd.get_opcode();
        let address_bytes =
            &cmd.get_address().to_be_bytes()[(4 - cmd.get_address_len()) as usize..];

        req.data[idx..idx + opcode_bytes.len()].clone_from_slice(opcode_bytes);
        idx += opcode_bytes.len();
        let mut addr_len = cmd.get_address_len();
        req.data[idx..idx + address_bytes.len()].clone_from_slice(address_bytes);
        idx += address_bytes.len();
        if cmd.get_switch() == eeprom::Switch::Mode111
            && cmd.get_dummy_cycles() % 8 == 0
            && addr_len + cmd.get_dummy_cycles() / 8 <= 7
        {
            // In cases when the number of dummy cycles is divisible by 8, stuff a number of
            // zero bytes after the address.  This allows debuggers without native support for
            // an arbitrary number of dummy cycles to perform the transaction.
            addr_len += cmd.get_dummy_cycles() / 8;
            for _ in 0..cmd.get_dummy_cycles() / 8 {
                req.data[idx] = 0x00;
                idx += 1;
            }
        } else if cmd.get_dummy_cycles() < 32 {
            req.flags |= (cmd.get_dummy_cycles() as u32) << EEPROM_FLAGS_DUMMY_CYCLES_POS
        } else {
            bail!(SpiError::InvalidDummyCycles(cmd.get_dummy_cycles()));
        }
        req.flags |= (addr_len as u32) << EEPROM_FLAGS_ADDR_LEN_POS;

        let data_start_offset = idx;
        // Optional write data bytes
        let databytes = std::cmp::min(USB_MAX_SIZE - 8 - data_start_offset, wbuf.len());
        req.data[data_start_offset..data_start_offset + databytes]
            .clone_from_slice(&wbuf[0..databytes]);
        self.usb_write_bulk(&req.as_bytes()[0..8 + data_start_offset + databytes])?;
        let mut index = databytes;

        while index < wbuf.len() {
            let mut req = CmdTransferContinue::new();
            req.data_index = index as u16;
            let databytes = std::cmp::min(USB_MAX_SIZE - 4, wbuf.len() - index);
            req.data[0..databytes].clone_from_slice(&wbuf[index..index + databytes]);
            self.usb_write_bulk(&req.as_bytes()[0..4 + databytes])?;
            index += databytes;
        }

        let next_stream_state = if rbuf.is_empty() {
            StreamState::PendingWrite
        } else {
            StreamState::PendingRead(rbuf)
        };
        if double_buffer {
            self.receive_streamed_data(stream_state)?;
            Ok(next_stream_state)
        } else {
            self.receive_streamed_data(next_stream_state)?;
            Ok(StreamState::NoPending)
        }
    }

    fn receive_streamed_data(&self, stream_state: StreamState) -> Result<()> {
        match stream_state {
            StreamState::NoPending => self.receive_first_streaming(),
            StreamState::PendingWrite => self.receive(&mut []),
            StreamState::PendingRead(rbuf) => self.receive(rbuf),
        }
    }

    fn eeprom_transmit_get_last_streamed_data(&self) -> Result<()> {
        let mut req = CmdEepromTransferStart::new();
        req.count = 0;
        req.flags = EEPROM_FLAGS_DOUBLE_BUFFER;
        self.usb_write_bulk(&req.as_bytes()[0..8])
    }

    fn get_last_streamed_data(&self, stream_state: StreamState) -> Result<()> {
        match stream_state {
            StreamState::NoPending => Ok(()),
            StreamState::PendingWrite => {
                self.eeprom_transmit_get_last_streamed_data()?;
                self.receive(&mut [])
            }
            StreamState::PendingRead(rbuf) => {
                self.eeprom_transmit_get_last_streamed_data()?;
                self.receive(rbuf)
            }
        }
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
        let mut buf2 = String::new();
        let captures = self
            .inner
            .cmd_one_line_output_match(
                &format!("spi info {}", &self.target_idx),
                &super::SPI_REGEX,
                &mut buf,
            )
            .or_else(|_| {
                self.inner.cmd_one_line_output_match(
                    &format!("spiget {}", &self.target_idx),
                    &super::SPI_REGEX,
                    &mut buf2,
                )
            })?;
        Ok(captures.get(3).unwrap().as_str().parse().unwrap())
    }
    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        self.inner
            .cmd_no_output(&format!("spi set speed {} {}", &self.target_idx, frequency))
            .or_else(|_| {
                self.inner
                    .cmd_no_output(&format!("spisetspeed {} {}", &self.target_idx, frequency))
            })
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        // The protocol imposes no limits to the number of Transfers
        // in a transaction.
        Ok(usize::MAX)
    }

    fn get_max_transfer_sizes(&self) -> Result<MaxSizes> {
        Ok(self.max_sizes)
    }

    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        let mut idx: usize = 0;
        self.select_my_spi_bus()?;

        // Simple cases involving using only a single USB command can be handled without explicit
        // embracing commands to hold CS asserted across a sequence of transfers, use that for
        // avoiding several USB roundtrips in the common cases.
        match transaction {
            [Transfer::Write(wbuf), Transfer::Read(rbuf)] => {
                // Hyperdebug can do SPI write followed by SPI read as a single USB
                // request/reply.  Take advantage of that by detecting pairs of
                // Transfer::Write followed by Transfer::Read.
                ensure!(
                    wbuf.len() <= self.max_sizes.write,
                    SpiError::InvalidDataLength(wbuf.len())
                );
                ensure!(
                    rbuf.len() <= self.max_sizes.read,
                    SpiError::InvalidDataLength(rbuf.len())
                );
                self.transmit(wbuf, rbuf.len())?;
                self.receive(rbuf)?;
                return Ok(());
            }
            [Transfer::Write(wbuf)] => {
                ensure!(
                    wbuf.len() <= self.max_sizes.write,
                    SpiError::InvalidDataLength(wbuf.len())
                );
                self.transmit(wbuf, 0)?;
                self.receive(&mut [])?;
                return Ok(());
            }
            [Transfer::Write(wbuf1), Transfer::Write(wbuf2)] => {
                if wbuf1.len() + wbuf2.len() <= self.max_sizes.write {
                    let mut combined_buf = vec![0u8; wbuf1.len() + wbuf2.len()];
                    combined_buf[..wbuf1.len()].clone_from_slice(wbuf1);
                    combined_buf[wbuf1.len()..].clone_from_slice(wbuf2);
                    self.transmit(&combined_buf, 0)?;
                    self.receive(&mut [])?;
                    return Ok(());
                }
            }
            [Transfer::Read(rbuf)] => {
                ensure!(
                    rbuf.len() <= self.max_sizes.read,
                    SpiError::InvalidDataLength(rbuf.len())
                );
                self.transmit(&[], rbuf.len())?;
                self.receive(rbuf)?;
                return Ok(());
            }
            _ => (),
        }

        // If control flow reaches this point, we have a more complicated sequence of operations,
        // and have to explicitly tell HyperDebug to keep the CS asserted while we issue each
        // command in turn.
        self.do_assert_cs(true)?;
        while idx < transaction.len() {
            match &mut transaction[idx..] {
                [Transfer::Write(wbuf), Transfer::Read(rbuf), ..] => {
                    ensure!(
                        wbuf.len() <= self.max_sizes.write,
                        SpiError::InvalidDataLength(wbuf.len())
                    );
                    ensure!(
                        rbuf.len() <= self.max_sizes.read,
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
                        wbuf.len() <= self.max_sizes.write,
                        SpiError::InvalidDataLength(wbuf.len())
                    );
                    self.transmit(wbuf, 0)?;
                    self.receive(&mut [])?;
                }
                [Transfer::Read(rbuf), ..] => {
                    ensure!(
                        rbuf.len() <= self.max_sizes.read,
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
                        wbuf.len() <= self.max_sizes.read && wbuf.len() <= self.max_sizes.write,
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

    fn run_eeprom_transactions(&self, mut transactions: &mut [eeprom::Transaction]) -> Result<()> {
        if self.feature_bitmap & FEATURE_BIT_EEPROM == 0 {
            // Debugger hardware/firmware does not support multi-lane extensions, attempt to
            // perform operation using basic SPI read/write.
            return eeprom::default_run_eeprom_transactions(self, transactions);
        }
        self.select_my_spi_bus()?;
        let mut stream_state = StreamState::NoPending;
        loop {
            match transactions {
                [eeprom::Transaction::Command(pre_cmd), eeprom::Transaction::Write(cmd, wbuf), eeprom::Transaction::WaitForBusyClear, rest @ ..] =>
                {
                    if pre_cmd.get_opcode().len() == 1 {
                        stream_state = self.eeprom_transmit(
                            Some(pre_cmd), /* write_enable */
                            cmd,
                            wbuf,
                            &mut [],
                            true, /* wait_for_busy_clear */
                            stream_state,
                        )?;
                    } else {
                        stream_state =
                            self.eeprom_transmit(None, pre_cmd, &[], &mut [], false, stream_state)?;
                        stream_state = self.eeprom_transmit(
                            None, /* write_enable */
                            cmd,
                            wbuf,
                            &mut [],
                            true, /* wait_for_busy_clear */
                            stream_state,
                        )?;
                    }
                    transactions = rest;
                }
                [eeprom::Transaction::Command(cmd), rest @ ..] => {
                    stream_state =
                        self.eeprom_transmit(None, cmd, &[], &mut [], false, stream_state)?;
                    transactions = rest;
                }
                [eeprom::Transaction::Read(cmd, ref mut rbuf), rest @ ..] => {
                    stream_state =
                        self.eeprom_transmit(None, cmd, &[], rbuf, false, stream_state)?;
                    transactions = rest;
                }
                [eeprom::Transaction::Write(cmd, wbuf), eeprom::Transaction::WaitForBusyClear, rest @ ..] =>
                {
                    stream_state = self.eeprom_transmit(
                        None, /* write_enable */
                        cmd,
                        wbuf,
                        &mut [],
                        true, /* wait_for_busy_clear */
                        stream_state,
                    )?;
                    transactions = rest;
                }
                [eeprom::Transaction::Write(cmd, wbuf), rest @ ..] => {
                    stream_state =
                        self.eeprom_transmit(None, cmd, wbuf, &mut [], false, stream_state)?;
                    transactions = rest;
                }
                [eeprom::Transaction::WaitForBusyClear, rest @ ..] => {
                    self.get_last_streamed_data(stream_state)?;
                    let mut status = eeprom::STATUS_WIP;
                    while status & eeprom::STATUS_WIP != 0 {
                        self.run_transaction(&mut [
                            Transfer::Write(&[eeprom::READ_STATUS]),
                            Transfer::Read(std::slice::from_mut(&mut status)),
                        ])?;
                    }
                    stream_state = StreamState::NoPending;
                    transactions = rest;
                }
                [] => {
                    return self.get_last_streamed_data(stream_state);
                }
            }
        }
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
