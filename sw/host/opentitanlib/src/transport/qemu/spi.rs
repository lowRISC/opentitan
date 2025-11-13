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
use crate::io::spi::{
    AssertChipSelect, MaxSizes, Target, TargetChipDeassert, Transfer, TransferMode,
};
use crate::transport::TransportError;
use crate::util::voltage::Voltage;

/// SPI clock polarity - unset = idle at low voltage, set = idle at high voltage.
const HEADER_CPOL_BIT: u8 = 0b01;
/// SPI phase - unset = sample when no longer idle, set = sample when idle.
const HEADER_CPHA_BIT: u8 = 0b10;
/// When set, CS is held asserted even after the current frame is transferred.
const HEADER_HOLD_CS_BIT: u8 = 0b1000_0000;

/// Maximum amount of SPI data that cam be transferred in one frame to QEMU (not including header).
const MAX_PACKET_LEN: usize = u16::MAX as usize;

/// The maximum amount of data that can be transferred to the device at once,
/// after which we must read out the returned data before continuing to send.
/// This is based on the default linux TTY buffer size of 4 KiB.
const MAX_TRANSMISSION_LEN: usize = 4096;

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
    ///
    /// The header is a custom format for our SPI device in QEMU.
    fn write_header(&self, len: u16, hold_cs: bool) -> anyhow::Result<()> {
        let mut tty = self.tty.borrow_mut();

        let spi_mode = match self.mode.get() {
            TransferMode::Mode0 => 0,
            TransferMode::Mode1 => HEADER_CPOL_BIT,
            TransferMode::Mode2 => HEADER_CPHA_BIT,
            TransferMode::Mode3 => HEADER_CPOL_BIT | HEADER_CPHA_BIT,
        };

        let hold_cs = match hold_cs {
            false => 0,
            true => HEADER_HOLD_CS_BIT,
        };

        // Assert chip select:
        write!(tty, "/CS")?;
        // Protocol version (zero):
        tty.write_all(&[0])?;
        // Flags:
        tty.write_all(&[spi_mode | hold_cs])?;
        // Ignored byte:
        tty.write_all(&[0])?;
        // Payload length:
        tty.write_all(&len.to_le_bytes())?;

        tty.flush()?;

        Ok(())
    }

    fn transfer(&self, wbuf: &[u8], rbuf: &mut [u8]) -> anyhow::Result<()> {
        for (wbuf_chunk, rbuf_chunk) in wbuf
            .chunks(MAX_TRANSMISSION_LEN)
            .zip(rbuf.chunks_mut(MAX_TRANSMISSION_LEN))
        {
            // Send outgoing data from the write buffer to QEMU
            self.tty
                .borrow_mut()
                .write_all(wbuf_chunk)
                .context("failed to read SPI TTY")?;

            // Read out the TX data from QEMU into the read buffer
            self.tty
                .borrow_mut()
                .read_exact(rbuf_chunk)
                .context("failed to read SPI TTY")?;
        }
        Ok(())
    }
}

impl Target for QemuSpi {
    fn run_transaction(&self, transaction: &mut [Transfer]) -> anyhow::Result<()> {
        // Send and receive over the TTY.
        let transfer_count = transaction.len();

        for (idx, transfer) in transaction.iter_mut().enumerate() {
            let last_transfer = idx + 1 == transfer_count;

            match transfer {
                Transfer::Read(buf) => {
                    let len: u16 = buf.len().try_into().context("read transfer too big")?;
                    self.write_header(len, !last_transfer)?;

                    // QEMU will only clock out the TX data if we send dummy data to the RX.
                    let dummy_buf = vec![0; buf.len()];
                    self.transfer(&dummy_buf, buf)?;
                }
                Transfer::Write(buf) => {
                    let len: u16 = buf.len().try_into().context("write transfer too big")?;
                    self.write_header(len, !last_transfer)?;

                    // Sending data will also clock out TX data from QEMU which we need
                    // to clear from the TTY. Read it into a buffer and drop it.
                    let mut garbage = vec![0; buf.len()];
                    self.transfer(buf, &mut garbage)?;
                }
                Transfer::Both(write_buf, read_buf) => {
                    ensure!(
                        write_buf.len() == read_buf.len(),
                        "transfers must be same size"
                    );
                    let len: u16 = write_buf.len().try_into().context("transfer too big")?;
                    self.write_header(len, !last_transfer)?;

                    self.transfer(write_buf, read_buf)?;
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
            read: MAX_PACKET_LEN,
            write: MAX_PACKET_LEN,
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
        // Could potentially be implemented by sending an empty packet that
        // holds the CS and another which deasserts when dropped.
        log::warn!("TODO: Implement CS for Qemu");
        Ok(AssertChipSelect::new(self))
    }

    fn set_voltage(&self, _voltage: Voltage) -> anyhow::Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn get_flashrom_programmer(&self) -> anyhow::Result<String> {
        Err(TransportError::UnsupportedOperation.into())
    }
}

impl TargetChipDeassert for QemuSpi {
    fn deassert_cs(&self) {}
}
