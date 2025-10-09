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
    pty: RefCell<TTYPort>,
    default_addr: Cell<Option<u8>>,
}

impl QemuI2c {
    pub fn new<P: AsRef<Path>>(pty: P) -> anyhow::Result<QemuI2c> {
        let pty = pty.as_ref().to_str().context("path not UTF-8")?;
        let pty = serialport::new(pty, 115200)
            .timeout(std::time::Duration::from_secs(1))
            .open_native()
            .context("failed to open I2C PTY")?;
        let pty = RefCell::new(pty);

        Ok(QemuI2c {
            pty,
            default_addr: Cell::new(None),
        })
    }
}

fn check_response<R: Read>(pty: &mut R, s: &'static str) -> anyhow::Result<()> {
    let mut byte_buf = [0u8; 1];
    pty.read_exact(&mut byte_buf)?;
    match byte_buf[0] {
        b'.' => Ok(()),
        b'!' => bail!(s),
        b'x' => bail!("Malformed command"),
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
        let target_addr = addr
            .or(self.default_addr.get())
            .ok_or(I2cError::MissingAddress)?;

        let mut pty = self.pty.borrow_mut();

        // Write and check protocol version
        let i2c_protocol_version = 1_u8;

        write!(pty, "i")?;
        pty.write_all(&[i2c_protocol_version])?;
        check_response(&mut *pty, "Protocol version mismatch")?;

        for transfer in transaction.iter_mut() {
            // Start/repeated start condition
            write!(pty, "S")?;

            match transfer {
                Transfer::Write(buf) => {
                    // Write I2C address + write bit (0)
                    let start_byte: u8 = target_addr << 1;
                    pty.write_all(std::slice::from_ref(&start_byte))?;
                    check_response(&mut *pty, "Write transfer NACKed")?;

                    // Write data byte and check for no NACKs
                    for byte in buf.iter() {
                        write!(pty, "W")?;
                        pty.write_all(std::slice::from_ref(byte))?;
                        check_response(&mut *pty, "Written byte NACKed")?;
                    }
                }

                Transfer::Read(buf) => {
                    // Write I2C address + read bit (1)
                    let start_byte: u8 = (target_addr << 1) | 1;
                    pty.write_all(std::slice::from_ref(&start_byte))?;
                    check_response(&mut *pty, "Read transfer NACKed")?;

                    // Issue read and read data byte
                    for byte in buf.iter_mut() {
                        write!(pty, "R")?;
                        pty.read_exact(std::slice::from_mut(byte))?;
                    }
                }
            }
        }
        // Stop condition
        write!(pty, "P")?;

        Ok(())
    }
}
