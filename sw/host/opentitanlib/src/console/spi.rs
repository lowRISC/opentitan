// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::time::Duration;

use crate::io::console::ConsoleDevice;
use crate::io::eeprom::AddressMode;
use crate::io::spi::Target;
use crate::spiflash::flash::SpiFlash;

pub struct SpiConsoleDevice<'a> {
    spi: &'a dyn Target,
    flash: SpiFlash,
    console_next_frame_number: Cell<u32>,
    rx_buf: RefCell<VecDeque<u8>>,
    next_read_address: Cell<u32>,
}

impl<'a> SpiConsoleDevice<'a> {
    const SPI_FRAME_HEADER_SIZE: usize = 12;
    const SPI_FLASH_READ_BUFFER_SIZE: u32 = 2048;
    const SPI_MAX_DATA_LENGTH: usize = 2036;
    const SPI_FRAME_MAGIC_NUMBER: u32 = 0xa5a5beef;
    const SPI_FLASH_PAYLOAD_BUFFER_SIZE: usize = 256;
    const SPI_TX_LAST_CHUNK_MAGIC_ADDRESS: u32 = 0x100;
    const SPI_BOOT_MAGIC_PATTERN: u32 = 0xcafeb002;

    pub fn new(spi: &'a dyn Target) -> Result<Self> {
        let mut flash = SpiFlash {
            ..Default::default()
        };
        flash.set_address_mode(spi, AddressMode::Mode3b)?;
        Ok(Self {
            spi,
            flash,
            rx_buf: RefCell::new(VecDeque::new()),
            console_next_frame_number: Cell::new(0),
            next_read_address: Cell::new(0),
        })
    }

    fn check_device_boot_up(&self, buf: &[u8]) -> Result<usize> {
        for i in (0..buf.len()).step_by(4) {
            let pattern: u32 = u32::from_le_bytes(buf[i..i + 4].try_into().unwrap());
            if pattern != SpiConsoleDevice::SPI_BOOT_MAGIC_PATTERN {
                return Ok(0);
            }
        }
        // Set busy bit and wait for the device to clear the boot magic.
        self.flash.program(self.spi, 0, buf)?;
        self.console_next_frame_number.set(0);
        self.next_read_address.set(0);
        Ok(0)
    }

    fn read_from_spi(&self) -> Result<usize> {
        // Read the SPI console frame header.
        let read_address = self.next_read_address.get();
        let mut header = vec![0u8; SpiConsoleDevice::SPI_FRAME_HEADER_SIZE];
        self.read_data(read_address, &mut header)?;

        let magic_number: u32 = u32::from_le_bytes(header[0..4].try_into().unwrap());
        let frame_number: u32 = u32::from_le_bytes(header[4..8].try_into().unwrap());
        let data_len_bytes: usize = u32::from_le_bytes(header[8..12].try_into().unwrap()) as usize;
        if magic_number != SpiConsoleDevice::SPI_FRAME_MAGIC_NUMBER
            || frame_number != self.console_next_frame_number.get()
            || data_len_bytes > SpiConsoleDevice::SPI_MAX_DATA_LENGTH
        {
            self.check_device_boot_up(&header)?;
            // This frame is junk, so we do not read the data
            return Ok(0);
        }
        self.console_next_frame_number.set(frame_number + 1);

        // Read the SPI console frame data.
        let data_len_bytes_w_pad = (data_len_bytes + 3) & !3;
        let mut data = vec![0u8; data_len_bytes_w_pad];
        let data_address: u32 = (read_address
            + u32::try_from(SpiConsoleDevice::SPI_FRAME_HEADER_SIZE).unwrap())
            % SpiConsoleDevice::SPI_FLASH_READ_BUFFER_SIZE;
        self.read_data(data_address, &mut data)?;

        let next_read_address: u32 = (read_address
            + u32::try_from(SpiConsoleDevice::SPI_FRAME_HEADER_SIZE + data_len_bytes_w_pad)
                .unwrap())
            % SpiConsoleDevice::SPI_FLASH_READ_BUFFER_SIZE;
        self.next_read_address.set(next_read_address);
        // Copy data to the internal data queue.
        self.rx_buf.borrow_mut().extend(&data[..data_len_bytes]);
        Ok(data_len_bytes)
    }

    fn read_data(&self, address: u32, buf: &mut [u8]) -> Result<&Self> {
        let buf_len: usize = buf.len();
        let space_to_end_of_buffer: usize =
            usize::try_from(SpiConsoleDevice::SPI_FLASH_READ_BUFFER_SIZE - address).unwrap();
        let first_part_size: usize = if buf_len > space_to_end_of_buffer {
            space_to_end_of_buffer
        } else {
            buf_len
        };
        self.flash
            .read(self.spi, address, &mut buf[0..first_part_size])?;
        // Handle wrap-around
        if first_part_size < buf_len {
            self.flash
                .read(self.spi, 0, &mut buf[first_part_size..buf_len])?;
        }
        Ok(self)
    }
}

impl<'a> ConsoleDevice for SpiConsoleDevice<'a> {
    fn console_read(&self, buf: &mut [u8], _timeout: Duration) -> Result<usize> {
        // Attempt to refill the internal data queue if it is empty.
        if self.rx_buf.borrow().is_empty() && self.read_from_spi()? == 0 {
            return Ok(0);
        }

        // Copy from the internal data queue to the output buffer.
        let mut i: usize = 0;
        while !self.rx_buf.borrow().is_empty() && i < buf.len() {
            buf[i] = self.rx_buf.borrow_mut().pop_front().unwrap();
            i += 1;
        }

        Ok(i)
    }

    fn console_write(&self, buf: &[u8]) -> Result<()> {
        let buf_len: usize = buf.len();
        let mut written_data_len: usize = 0;
        while written_data_len < buf_len {
            let mut write_address = SpiConsoleDevice::SPI_TX_LAST_CHUNK_MAGIC_ADDRESS;
            let mut data_len: usize = buf_len - written_data_len;

            if data_len > SpiConsoleDevice::SPI_FLASH_PAYLOAD_BUFFER_SIZE {
                data_len = SpiConsoleDevice::SPI_FLASH_PAYLOAD_BUFFER_SIZE;
                write_address = 0;
            }

            self.flash.program(
                self.spi,
                write_address,
                &buf[written_data_len..written_data_len + data_len],
            )?;
            written_data_len += data_len;
        }

        Ok(())
    }
}
