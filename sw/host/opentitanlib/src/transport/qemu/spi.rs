// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};
use std::io::{Read, Write};
use std::path::Path;
use std::rc::Rc;

use anyhow::{Context, ensure};
use serialport::TTYPort;

use crate::io::gpio;
use crate::io::spi::{AssertChipSelect, MaxSizes, Target, Transfer, TransferMode};
use crate::transport::TransportError;
use crate::util::voltage::Voltage;

pub struct QemuSpi {
    tty: RefCell<TTYPort>,

    mode: Cell<TransferMode>,
}

impl QemuSpi {
    pub fn new<P: AsRef<Path>>(tty: P) -> anyhow::Result<QemuSpi> {
        let tty = tty.as_ref().to_str().context("path not UTF-8")?;
        let tty = serialport::new(tty, 115200)
            .timeout(std::time::Duration::from_secs(1))
            .open_native()
            .context("failed to open SPI TTY")?;
        let tty = RefCell::new(tty);

        let mode = Cell::new(TransferMode::Mode0);

        Ok(QemuSpi { tty, mode })
    }

    /// Send a SPI transfer header to QEMU.
    ///
    /// Takes the length of the transfer and whether the CS should be held
    /// asserted afterwards or released.
    fn write_header(&self, len: u16, hold_cs: bool) -> anyhow::Result<()> {
        let mut tty = self.tty.borrow_mut();

        let mode = match self.mode.get() {
            TransferMode::Mode0 => 0b00,
            TransferMode::Mode1 => 0b01,
            TransferMode::Mode2 => 0b10,
            TransferMode::Mode3 => 0b11,
        };

        let hold_cs = match hold_cs {
            true => 1 << 7,
            false => 0,
        };

        // Assert chip select:
        write!(tty, "/CS")?;
        // Protocol version (zero):
        tty.write_all(&[0])?;
        // Mode and flags:
        tty.write_all(&[mode | hold_cs])?;
        // Ignored byte:
        tty.write_all(&[0])?;
        // Payload length:
        tty.write_all(&len.to_le_bytes())?;

        tty.flush()?;

        Ok(())
    }
}

impl Target for QemuSpi {
    fn run_transaction(&self, transaction: &mut [Transfer]) -> anyhow::Result<()> {
        // Send and receive over the TTY.
        let transfer_count = transaction.len();

        for (idx, transfer) in transaction.into_iter().enumerate() {
            let last_transfer = idx + 1 == transfer_count;

            match transfer {
                Transfer::Read(buf) => {
                    let len: u16 = buf.len().try_into().context("read transfer too big")?;
                    self.write_header(len, !last_transfer)?;

                    // QEMU will only clock out the TX data if we send dummy data to the
                    // RX. We can use the read buffer for this.
                    self.tty
                        .borrow_mut()
                        .write_all(buf)
                        .context("failed to read SPI TTY")?;
                    self.tty.borrow_mut().flush()?;

                    // Read out the TX data from QEMU:
                    self.tty
                        .borrow_mut()
                        .read_exact(buf)
                        .context("failed to read SPI TTY")?;
                }
                Transfer::Write(buf) => {
                    let len: u16 = buf.len().try_into().context("write transfer too big")?;
                    self.write_header(len, !last_transfer)?;

                    // Send RX data to QEMU:
                    self.tty
                        .borrow_mut()
                        .write_all(buf)
                        .context("failed to write to SPI TTY")?;
                    self.tty.borrow_mut().flush()?;

                    // Sending data will also clock out TX data from QEMU which we need
                    // to clear from the TTY. Read it into a buffer and drop it:
                    let mut garbage = vec![0; buf.len()];
                    self.tty.borrow_mut().read_exact(&mut garbage)?;
                }
                Transfer::Both(write_buf, read_buf) => {
                    ensure!(
                        write_buf.len() == read_buf.len(),
                        "transfers must be same size"
                    );
                    let len: u16 = write_buf.len().try_into().context("transfer too big")?;
                    self.write_header(len, !last_transfer)?;

                    self.tty
                        .borrow_mut()
                        .write_all(write_buf)
                        .context("failed to write to SPI TTY")?;
                    self.tty.borrow_mut().flush()?;

                    self.tty
                        .borrow_mut()
                        .read_exact(read_buf)
                        .context("failed to read from SPI TTY")?;
                }
            }
        }

        Ok(())
    }

    fn get_bits_per_word(&self) -> anyhow::Result<u32> {
        Ok(32)
    }

    fn supports_bidirectional_transfer(&self) -> anyhow::Result<bool> {
        Ok(true)
    }

    fn get_max_transfer_count(&self) -> anyhow::Result<usize> {
        Ok(0)
    }

    fn get_max_transfer_sizes(&self) -> anyhow::Result<MaxSizes> {
        let sizes = MaxSizes {
            read: (1 << 16) - 1,
            write: (1 << 16) - 1,
        };
        Ok(sizes)
    }

    fn get_transfer_mode(&self) -> anyhow::Result<TransferMode> {
        Ok(self.mode.get())
    }

    fn set_transfer_mode(&self, mode: TransferMode) -> anyhow::Result<()> {
        self.mode.set(mode);
        Ok(())
    }

    fn get_max_speed(&self) -> anyhow::Result<u32> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn set_max_speed(&self, _max_speed: u32) -> anyhow::Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn set_bits_per_word(&self, _bits_per_word: u32) -> anyhow::Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn set_pins(
        &self,
        _serial_clock: Option<&Rc<dyn gpio::GpioPin>>,
        _host_out_device_in: Option<&Rc<dyn gpio::GpioPin>>,
        _host_in_device_out: Option<&Rc<dyn gpio::GpioPin>>,
        _chip_select: Option<&Rc<dyn gpio::GpioPin>>,
    ) -> anyhow::Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn assert_cs(self: Rc<Self>) -> anyhow::Result<AssertChipSelect> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn set_voltage(&self, _voltage: Voltage) -> anyhow::Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn get_flashrom_programmer(&self) -> anyhow::Result<String> {
        Err(TransportError::UnsupportedOperation.into())
    }
}
