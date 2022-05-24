// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, Result};
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use structopt::clap::arg_enum;
use thiserror::Error;

use crate::io::i2c;
use crate::io::spi;

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
}

/// Low level interface for accessing TPM.  Separate implementations exist for SPI and I2C.
pub trait Driver {
    /// Read from the given TPM register, number of bytes to read given by length of data slice.
    fn read_register(&self, register: Register, data: &mut [u8]) -> Result<()>;
    /// Write to the given TPM register.
    fn write_register(&self, register: Register, data: &[u8]) -> Result<()>;
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
}

const SPI_TPM_READ: u32 = 0xC0000000;
const SPI_TPM_DATA_LEN_POS: u8 = 23;
const SPI_TPM_ADDRESS_OFFSET: u32 = 0x00D40000;

impl Driver for SpiDriver {
    fn read_register(&self, register: Register, data: &mut [u8]) -> Result<()> {
        let _cs_asserted = Rc::clone(&self.spi).assert_cs()?; // Deasserts when going out of scope.
        let mut buffer = vec![0u8; 4];
        let req: u32 = SPI_TPM_READ
            | ((data.len() as u32 - 1) << SPI_TPM_DATA_LEN_POS)
            | SPI_TPM_ADDRESS_OFFSET
            | (Self::addr(register) as u32);
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
        self.spi.run_transaction(&mut [spi::Transfer::Read(data)])?;
        Ok(())
    }

    fn write_register(&self, _register: Register, _data: &[u8]) -> Result<()> {
        bail!(anyhow!("Unimplemented"))
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
        self.i2c.run_transaction(
            self.addr,
            &mut [
                i2c::Transfer::Write(&[Self::addr(register).unwrap()]),
                i2c::Transfer::Read(data),
            ],
        )?;
        Ok(())
    }

    fn write_register(&self, register: Register, data: &[u8]) -> Result<()> {
        let mut buffer = vec![Self::addr(register).unwrap()];
        buffer.extend_from_slice(data);
        self.i2c
            .run_transaction(self.addr, &mut [i2c::Transfer::Write(&buffer)])?;
        Ok(())
    }
}
