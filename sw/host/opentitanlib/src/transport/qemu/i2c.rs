// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};
use std::io::{Read, Write};
use std::path::Path;

use anyhow::Context;
use anyhow::bail;
use serialport::TTYPort;

use crate::io::i2c::I2cError;
use crate::io::i2c::{Bus, Transfer};
use crate::transport::TransportError;

pub struct QemuI2c {
    tty: RefCell<TTYPort>,
    default_addr: Cell<Option<u8>>,
}

impl QemuI2c {
    pub fn new<P: AsRef<Path>>(tty: P) -> anyhow::Result<QemuI2c> {
        let tty = tty.as_ref().to_str().context("path not UTF-8")?;
        let tty = serialport::new(tty, 115200)
            .timeout(std::time::Duration::from_secs(1))
            .open_native()
            .context("failed to open I2C TTY")?;
        let tty = RefCell::new(tty);

        Ok(QemuI2c {
            tty,
            default_addr: Cell::new(None),
        })
    }
}

fn check_ack<R: Read>(tty: &mut R) -> anyhow::Result<()> {
    let mut byte_buf = [0u8; 1];
    tty.read_exact(&mut byte_buf)?;
    match byte_buf[0] {
        b'.' => Ok(()),
        b'!' => bail!("Unexpected NACK"),
        _ => unreachable!(),
    }
}

impl Bus for QemuI2c {
    fn get_max_speed(&self) -> anyhow::Result<u32> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn set_max_speed(&self, _max_speed: u32) -> anyhow::Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn set_default_address(&self, addr: u8) -> anyhow::Result<()> {
        self.default_addr.set(Some(addr));
        Ok(())
    }

    fn run_transaction(
        &self,
        addr: Option<u8>,
        transaction: &mut [Transfer],
    ) -> anyhow::Result<()> {
        let addr = addr
            .or(self.default_addr.get())
            .ok_or(I2cError::MissingAddress)?;

        let mut tty = self.tty.borrow_mut();

        for transfer in transaction.iter_mut() {
            // Start/repeated start condition
            write!(tty, "s")?;

            match transfer {
                Transfer::Write(buf) => {
                    // Write I2C address + write bit (0)
                    let start_byte: u8 = addr << 1;
                    tty.write_all(std::slice::from_ref(&start_byte))?;
                    check_ack(&mut *tty)?;

                    // Write data byte and check for no NACKs
                    for byte in buf.iter() {
                        write!(tty, "W")?;
                        tty.write_all(std::slice::from_ref(byte))?;
                        check_ack(&mut *tty)?;
                    }
                }

                Transfer::Read(buf) => {
                    // Write I2C address + read bit (1)
                    let start_byte: u8 = (addr << 1) | 1;
                    tty.write_all(std::slice::from_ref(&start_byte))?;
                    check_ack(&mut *tty)?;

                    // Issue read and read data byte
                    for byte in buf.iter_mut() {
                        write!(tty, "R")?;
                        tty.read_exact(std::slice::from_mut(byte))?;
                    }
                }
            }
        }
        // Stop condition
        write!(tty, "S")?;

        Ok(())
    }
}
