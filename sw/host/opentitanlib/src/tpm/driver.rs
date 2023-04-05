// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use std::thread;
use std::time::{Duration, Instant};
use structopt::clap::arg_enum;
use thiserror::Error;

use crate::io::i2c;
use crate::io::spi;
use crate::tpm::access::TpmAccess;
use crate::tpm::status::TpmStatus;

arg_enum! {
    /// Tpm registers, can be specified in command line arguments.
    #[allow(non_camel_case_types)]
    #[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
    pub enum Register {
        ACCESS,
        INT_ENABLE,
        INT_VECTOR,
        INT_STATUS,
        INTF_CAPABILITY,
        STS,
        DATA_FIFO,
        INTERFACE_ID,
        XDATA_FIFO,
        DID_VID,
        RID,
    }
}

impl Register {
    /// Size of given TPM register in bytes, `None` means variable size.
    pub fn size(&self) -> Option<usize> {
        Some(match *self {
            Self::ACCESS => 1,
            Self::INT_ENABLE => 4,
            Self::INT_VECTOR => 4,
            Self::INT_STATUS => 4,
            Self::INTF_CAPABILITY => 4,
            Self::STS => 4,
            Self::DATA_FIFO => return None,
            Self::INTERFACE_ID => 4,
            Self::XDATA_FIFO => return None,
            Self::DID_VID => 4,
            Self::RID => 4,
        })
    }
}

/// Errors relating to TPM communication.
#[derive(Error, Debug)]
pub enum TpmError {
    #[error("TPM timeout")]
    Timeout,
    #[error("Unexpected response size {0}")]
    UnexpectedResponseSize(usize),
    #[error("Response incomplete. Missing {0} bytes.")]
    ResponseIncomplete(usize),
    #[error("Failed to get status")]
    ReadStatusFail,
    #[error("Timeout polling for response")]
    ResponseTimeout,
}

/// Low level interface for accessing TPM.  Separate implementations exist for SPI and I2C.
pub trait Driver {
    /// Initialize the TPM by claiming the access register.
    fn init(&self) -> Result<()> {
        self.write_register(
            Register::ACCESS,
            &TpmAccess::ACTIVE_LOCALITY.bits().to_be_bytes(),
        )?;
        self.write_register(
            Register::ACCESS,
            &TpmAccess::REQUEST_USE.bits().to_be_bytes(),
        )?;
        Ok(())
    }

    /// Read from the given TPM register, number of bytes to read given by length of data slice.
    fn read_register(&self, register: Register, data: &mut [u8]) -> Result<()>;

    /// Write to the given TPM register.
    fn write_register(&self, register: Register, data: &[u8]) -> Result<()>;

    /// Execute a TPM command and return the result as a Vec<u8> or time out.
    fn execute_command(&self, cmd: &[u8]) -> Result<Vec<u8>> {
        self.write_register(Register::STS, &TpmStatus::CMD_READY.to_le_bytes())?;

        log::debug!("RUN({}) {:02X?}", cmd.len(), cmd);
        self.poll_for_ready()?;
        for slice in cmd.chunks(MAX_TRANSACTION_SIZE) {
            self.write_register(Register::DATA_FIFO, slice)?;
        }
        self.write_register(Register::STS, &TpmStatus::TPM_GO.to_le_bytes())?;

        let sz = self
            .poll_for_data_available()?
            .burst_count()
            .max(RESPONSE_HEADER_SIZE)
            .min(MAX_TRANSACTION_SIZE);
        let mut result: Vec<u8> = vec![0; sz];
        self.read_register(Register::DATA_FIFO, result.as_mut_slice())?;
        let resp_size: usize = u32::from_be_bytes(result[2..6].try_into().unwrap()) as usize;
        ensure!(
            resp_size < MAX_RESPONSE_SIZE,
            TpmError::UnexpectedResponseSize(resp_size)
        );
        let mut remaining = resp_size - sz;

        let mut sts = self.read_status()?;
        while sts.is_valid() && sts.data_available() && remaining > 0 {
            let to_read: usize = remaining.min(MAX_TRANSACTION_SIZE);
            let mut result2: Vec<u8> = vec![0; to_read];
            self.read_register(Register::DATA_FIFO, result2.as_mut_slice())?;
            result.append(&mut result2);
            remaining -= to_read;
            sts = self.read_status()?;
        }
        ensure!(remaining == 0, TpmError::ResponseIncomplete(remaining));
        log::debug!("RES({}) {:02X?}", result.len(), result.as_slice());

        // Return to idle state.
        self.write_register(Register::STS, &TpmStatus::CMD_READY.to_le_bytes())?;

        Ok(result)
    }

    /// Fetches the current status.
    fn read_status(&self) -> Result<TpmStatus> {
        let mut out = [0u8; 4];
        let res = self.read_register(Register::STS, &mut out);
        if res.is_ok() {
            Ok(TpmStatus::from_bytes(out))
        } else {
            log::error!("Failed to read status");
            Err(TpmError::ReadStatusFail.into())
        }
    }

    /// Poll the status register until the status is valid and data is available or time out.
    fn poll_for_data_available(&self) -> Result<TpmStatus> {
        const STATUS_POLL_TIMEOUT: Duration = Duration::from_millis(30000);
        let deadline = Instant::now() + STATUS_POLL_TIMEOUT;
        let mut sts = self.read_status()?;
        // If the device is busy and doesn't actually respond, the status comes back as !0. This
        // will look like a valid status with a full FIFO, so ignore this case.
        while !sts.is_valid()
            || !sts.data_available()
            || sts.raw_value() == !0
            // Sometimes the status returns shifted. Detect that here.
            || (sts.raw_value() & 0xFF) == 0xFF
        {
            if Instant::now() > deadline {
                log::error!("Status poll timeout.");
                return Err(TpmError::ResponseTimeout.into());
            }
            sts = self.read_status()?;
            thread::sleep(Duration::from_millis(10));
        }
        Ok(sts)
    }

    /// Poll the status register until the status is valid and the tpm is ready or time out.
    fn poll_for_ready(&self) -> Result<TpmStatus> {
        const STATUS_POLL_TIMEOUT: Duration = Duration::from_millis(30000);
        let deadline = Instant::now() + STATUS_POLL_TIMEOUT;
        let mut sts = self.read_status()?;
        // If the device is busy and doesn't actually respond, the status comes back as !0. This
        // will look like a valid status with a full FIFO, so ignore this case.
        while !sts.is_valid()
            || !sts.is_ready()
            || sts.raw_value() == !0
            // Sometimes the status returns shifted. Detect that here.
            || (sts.raw_value() & 0xFF) == 0xFF
        {
            ensure!(Instant::now() <= deadline, TpmError::Timeout);
            sts = self.read_status()?;
            thread::sleep(Duration::from_millis(10));
        }
        Ok(sts)
    }
}

/// Implementation of the low level interface via standard SPI protocol.
pub struct SpiDriver {
    spi: Rc<dyn spi::Target>,
}

impl SpiDriver {
    pub fn new(spi: Rc<dyn spi::Target>) -> Self {
        Self { spi }
    }

    /// Numerical TPM register address as used in SPI protocol.
    pub fn addr(register: Register) -> u16 {
        match register {
            Register::ACCESS => 0x0000,
            Register::INT_ENABLE => 0x0008,
            Register::INT_VECTOR => 0x000C,
            Register::INT_STATUS => 0x0010,
            Register::INTF_CAPABILITY => 0x0014,
            Register::STS => 0x0018,
            Register::DATA_FIFO => 0x0024,
            Register::INTERFACE_ID => 0x0030,
            Register::XDATA_FIFO => 0x0080,
            Register::DID_VID => 0x0F00,
            Register::RID => 0x0F04,
        }
    }

    /// Write a transaction header for the given register and length.
    fn write_header(&self, register: Register, len: usize, is_read: bool) -> Result<()> {
        let mut buffer = vec![0u8; 4];
        let mut req: u32 = ((len as u32 - 1) << SPI_TPM_DATA_LEN_POS)
            | SPI_TPM_ADDRESS_OFFSET
            | (Self::addr(register) as u32);
        if is_read {
            req |= SPI_TPM_READ;
        } else {
            req |= SPI_TPM_WRITE;
        }
        self.spi
            .run_transaction(&mut [spi::Transfer::Both(&req.to_be_bytes(), &mut buffer)])?;
        if buffer[3] & 1 == 0 {
            let mut retries = 10;
            while {
                self.spi
                    .run_transaction(&mut [spi::Transfer::Read(&mut buffer[0..1])])?;
                buffer[0] & 1 == 0
            } {
                retries -= 1;
                if retries == 0 {
                    bail!(TpmError::Timeout)
                }
            }
        }
        Ok(())
    }
}

const SPI_TPM_READ: u32 = 0xC0000000;
const SPI_TPM_WRITE: u32 = 0x40000000;
const SPI_TPM_DATA_LEN_POS: u8 = 24;
const SPI_TPM_ADDRESS_OFFSET: u32 = 0x00D40000;

const MAX_TRANSACTION_SIZE: usize = 32;
const RESPONSE_HEADER_SIZE: usize = 6;
const MAX_RESPONSE_SIZE: usize = 4096;

impl Driver for SpiDriver {
    fn read_register(&self, register: Register, data: &mut [u8]) -> Result<()> {
        let _cs_asserted = Rc::clone(&self.spi).assert_cs()?; // Deasserts when going out of scope.
        self.write_header(register, data.len(), true)?;
        self.spi.run_transaction(&mut [spi::Transfer::Read(data)])?;
        Ok(())
    }

    fn write_register(&self, register: Register, data: &[u8]) -> Result<()> {
        let _cs_asserted = Rc::clone(&self.spi).assert_cs()?; // Deasserts when going out of scope.
        self.write_header(register, data.len(), false)?;
        self.spi
            .run_transaction(&mut [spi::Transfer::Write(data)])?;
        Ok(())
    }
}

/// Implementation of the low level interface via Google I2C protocol.
pub struct I2cDriver {
    i2c: Rc<dyn i2c::Bus>,
    addr: u8,
}

impl I2cDriver {
    pub fn new(i2c: Rc<dyn i2c::Bus>, addr: u8) -> Self {
        Self { i2c, addr }
    }

    /// Numerical TPM register address as used in Google I2C protocol.
    pub fn addr(reg: Register) -> Option<u8> {
        match reg {
            Register::ACCESS => Some(0x00),
            Register::STS => Some(0x01),
            Register::DATA_FIFO => Some(0x05),
            Register::DID_VID => Some(0x06),
            _ => None,
        }
    }
}

impl Driver for I2cDriver {
    fn read_register(&self, register: Register, data: &mut [u8]) -> Result<()> {
        const MAX_TRIES: usize = 10;
        let mut count = 0;
        // Retry in case the I2C bus wasn't ready.
        let res = loop {
            count += 1;
            let res = self.i2c.run_transaction(
                self.addr,
                &mut [
                    i2c::Transfer::Write(&[Self::addr(register).unwrap()]),
                    i2c::Transfer::Read(data),
                ],
            );
            match res {
                Err(e) => {
                    log::trace!(
                        "Register 0x{:X} access error: {}",
                        Self::addr(register).unwrap(),
                        e
                    );
                    if count == MAX_TRIES {
                        break Err(e);
                    }
                }
                Ok(()) => {
                    if count > 1 {
                        log::trace!("Success after {} tries.", count);
                    }
                    break Ok(());
                }
            }
            thread::sleep(Duration::from_millis(100));
        };
        if res.is_err() {
            log::error!("Failed to read TPM register.");
        }
        res
    }

    fn write_register(&self, register: Register, data: &[u8]) -> Result<()> {
        let mut buffer = vec![Self::addr(register).unwrap()];
        buffer.extend_from_slice(data);
        self.i2c
            .run_transaction(self.addr, &mut [i2c::Transfer::Write(&buffer)])?;
        Ok(())
    }
}
