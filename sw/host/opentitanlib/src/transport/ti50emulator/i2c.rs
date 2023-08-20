// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Context, Result};
use log;

use std::cell::{Cell, RefCell};
use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::{Duration, Instant};

use crate::io::emu::EmuState;
use crate::io::i2c::{Bus, I2cError, Transfer};
use crate::transport::ti50emulator::emu::EMULATOR_INVALID_ID;
use crate::transport::ti50emulator::Inner;
use crate::transport::TransportError;

const MAX_READ_TIMEOUT: Duration = Duration::from_millis(35);
const MAX_WRITE_TIMEOUT: Duration = Duration::from_millis(35);

const TI50_I2C_BUS_WRITE_REQ: u8 = b'W';
const TI50_I2C_BUS_READ_REQ: u8 = b'R';
const TI50_I2C_BUS_WRITE_RES: u8 = b'w';
const TI50_I2C_BUS_READ_RES: u8 = b'r';

/// Structure representing the emulated I2C BUS control packet encoder/decoder
/// The current implementation does not require the use of a low-level
/// representation with ACK/NACK bits. However, a minimal data separation
/// between successive transactions is required.
struct Ti50BusControl {}

////////////////////////////////////////////////////////////////////////////////
// Emulated I2C BUS data flow:
//
// [NAME] - named byte.
// [####] - long sequence of data bytes
// Tx - Direction of transfer - From Host (OpenTitanTool) to Target (chip).
// Rx - Direction of transfer - From Target (chip) to Target (chip).
//
// (1) Write transfer
//                         /--2B--\/----------LEN_BE-----------\   deadline->|
//                         |      ||                           |             |
// Tx <<< [WRITE_REQ][ADDR][LEN_BE][###########################]+------------|-
//                                                              |            |
//                                                              |            |
//                                                              |            |
// Rx >>> ------------------------------------------------------+[WRITE_RES]-|-
//
// Note: There is possibility that the data will get stuck in UnixStreamSocket
// buffer so we have to wait for WRITE_RES before starting next transaction.
//
// (2) Read transfer
//
//                        /--2B--\                         deadline->|
//                        |      |                                   |
// Tx <<< [READ_REQ][ADDR][LEN_BE]+----------------------------------|---------
//                                |                                  |
//                                |          /-----LEN_BE-----\      |
//                                |          |                |      |
// Rx >>> ------------------------+[READ_RES][################]------|---------
//
// Note: In the case of a read operation, LEN_BE represents the number of bytes
// the DUT would normally respond with an ACK signal
//
////////////////////////////////////////////////////////////////////////////////

impl Ti50BusControl {
    /// Send write request
    pub fn send_write_request(
        fd: &mut UnixStream,
        deadline: Instant,
        addr: u8,
        len: u16,
    ) -> Result<()> {
        let mut header = [TI50_I2C_BUS_WRITE_REQ, addr, 0, 0];
        header[2..].copy_from_slice(&len.to_be_bytes());
        Ti50I2cBus::tx(fd, &header, deadline)
    }

    /// Send read request
    pub fn send_read_request(
        fd: &mut UnixStream,
        deadline: Instant,
        addr: u8,
        len: u16,
    ) -> Result<()> {
        let mut header = [TI50_I2C_BUS_READ_REQ, addr, 0, 0];
        header[2..].copy_from_slice(&len.to_be_bytes());
        Ti50I2cBus::tx(fd, &header, deadline)
    }

    /// Receive write response
    pub fn recv_write_response(fd: &mut UnixStream, deadline: Instant) -> Result<()> {
        let buf = &mut [1u8; 1];
        let _rx_len = Ti50I2cBus::rx(fd, &mut buf[..], deadline)?;
        match buf {
            [TI50_I2C_BUS_WRITE_RES] => Ok(()),
            [raw] => Err(
                I2cError::Generic(format!("Unexpected BUS control message: {:02X}", raw)).into(),
            ),
        }
    }

    /// Receive read response
    pub fn recv_read_response(fd: &mut UnixStream, deadline: Instant) -> Result<()> {
        let buf = &mut [1u8; 1];
        let _rx_len = Ti50I2cBus::rx(fd, &mut buf[..], deadline)?;
        match buf {
            [TI50_I2C_BUS_READ_RES] => Ok(()),
            [raw] => Err(
                I2cError::Generic(format!("Unexpected BUS control message: {:02X}", raw)).into(),
            ),
        }
    }
}

/// Structure representing Emulated I2C BUS
pub struct Ti50I2cBus {
    inner: Rc<Inner>,
    // This socket is valid as long as SubProcess is running.
    socket: RefCell<Option<UnixStream>>,
    // full path to socket file
    path: PathBuf,
    // last SubProcess ID
    last_id: Cell<u64>,
    default_address: Cell<Option<u8>>,
}

impl Ti50I2cBus {
    /// Create new instance of [`Ti50I2cBus`] based on provided parameters.
    pub fn open(inner: &Rc<Inner>, path: &str) -> Result<Self> {
        let soc_path = inner.process.borrow().get_runtime_dir().join(path);
        Ok(Self {
            inner: inner.clone(),
            socket: RefCell::default(),
            path: soc_path,
            last_id: Cell::new(EMULATOR_INVALID_ID),
            default_address: Cell::new(None),
        })
    }

    /// Function re-connect socket to `SubProcess` when detect
    /// that process was restarted.
    pub fn reconnect(&self) -> Result<()> {
        let mut socket = self.socket.borrow_mut();
        let id = self.inner.process.borrow().get_id();
        if self.last_id.get() != id {
            let fd =
                UnixStream::connect(&self.path).context(format!("Pipe path: {:?}", &self.path))?;
            *socket = Some(fd);
            self.last_id.set(id);
        }
        Ok(())
    }

    /// Function check if I2C transaction should be performed on DUT.
    pub fn check_state(&self) -> Result<()> {
        let process = &mut self.inner.process.borrow_mut();
        process.update_status()?;
        match process.get_state() {
            EmuState::On => Ok(()),
            state => Err(I2cError::Generic(format!(
                "Operation not supported in Emulator state: {}",
                state
            ))
            .into()),
        }
    }

    /// Function try to receive data from unix socket.
    pub fn rx(fd: &mut UnixStream, data: &mut [u8], deadline: Instant) -> Result<usize> {
        let mut rx_count: usize = 0;
        while rx_count <= data.len() {
            let ts = Instant::now();
            if ts > deadline {
                bail!(I2cError::Timeout);
            }
            fd.set_read_timeout(Some(deadline - ts))?;
            rx_count += fd.read(&mut data[rx_count..])?;
        }
        Ok(rx_count)
    }

    /// Function send contents of slice to unix socket.
    pub fn tx(fd: &mut UnixStream, data: &[u8], deadline: Instant) -> Result<()> {
        let mut tx_count: usize = 0;
        while tx_count <= data.len() {
            let ts = Instant::now();
            if ts > deadline {
                bail!(I2cError::Timeout);
            }
            fd.set_write_timeout(Some(deadline - ts))?;
            tx_count += fd.write(&data[tx_count..])?;
        }
        Ok(())
    }

    /// Function perform write transaction on emulated bus.
    pub fn write(&self, addr: u8, data: &[u8]) -> Result<()> {
        if let Some(ref mut fd) = *self.socket.borrow_mut() {
            let deadline = Instant::now() + MAX_WRITE_TIMEOUT;
            log::debug!(
                "I2C Transmit transaction write request addr: {:02X} len: {}",
                addr,
                data.len()
            );
            Ti50BusControl::send_write_request(fd, deadline, addr, data.len() as u16)?;
            Ti50I2cBus::tx(fd, data, deadline)?;
            return Ti50BusControl::recv_write_response(fd, deadline);
        }
        bail!(I2cError::Generic("Invalid socket".to_string()));
    }

    /// Function perform read transaction on emulated BUS.
    pub fn read(&self, addr: u8, data: &mut [u8]) -> Result<()> {
        if let Some(ref mut fd) = *self.socket.borrow_mut() {
            let deadline = Instant::now() + MAX_READ_TIMEOUT;
            log::debug!(
                "I2C Transmit transaction read request addr: {:02X} len: {}",
                addr,
                data.len()
            );
            Ti50BusControl::send_read_request(fd, deadline, addr, data.len() as u16)?;
            Ti50BusControl::recv_read_response(fd, deadline)?;
            Ti50I2cBus::rx(fd, &mut data[..], deadline)?;
            return Ok(());
        }
        bail!(I2cError::Generic("Invalid socket".to_string()));
    }
}

impl Bus for Ti50I2cBus {
    /// Gets the maximum allowed speed of the I2C bus.
    fn get_max_speed(&self) -> Result<u32> {
        bail!(TransportError::UnsupportedOperation)
    }

    /// Sets the maximum allowed speed of the I2C bus, typical values are 100_000, 400_000 or
    /// 1_000_000.
    fn set_max_speed(&self, _max_speed: u32) -> Result<()> {
        bail!(TransportError::UnsupportedOperation)
    }

    fn set_default_address(&self, addr: u8) -> Result<()> {
        self.default_address.set(Some(addr));
        Ok(())
    }

    fn run_transaction(&self, addr: Option<u8>, transaction: &mut [Transfer]) -> Result<()> {
        let addr = addr.or(self.default_address.get()).unwrap(); // TODO: Handle None
        self.check_state()?;
        self.reconnect()?;
        for transfer in transaction {
            match transfer {
                Transfer::Write(wr) => {
                    self.write(addr, wr)?;
                }
                Transfer::Read(rd) => {
                    self.read(addr, rd)?;
                }
            }
        }
        Ok(())
    }
}
