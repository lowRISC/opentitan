// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::time::Duration;

use crate::io::console::ConsoleDevice;
use crate::io::spi::{Target, Transfer};

pub struct SpiConsoleDevice<'a> {
    spi: &'a dyn Target,
    console_next_frame_number: Cell<u32>,
    rx_buf: RefCell<VecDeque<u8>>,
}

impl<'a> SpiConsoleDevice<'a> {
    const SPI_FRAME_HEADER_SIZE: usize = 8;
    const SPI_MAX_DATA_LENGTH: usize = 2032;

    pub fn new(spi: &'a dyn Target) -> Self {
        Self {
            spi,
            rx_buf: RefCell::new(VecDeque::new()),
            console_next_frame_number: Cell::new(0),
        }
    }

    fn read_from_spi(&self) -> Result<usize> {
        // Read the SPI console frame header.
        let mut header = vec![0u8; SpiConsoleDevice::SPI_FRAME_HEADER_SIZE];
        self.spi
            .run_transaction(&mut [Transfer::Write(&[0xff; 4]), Transfer::Read(&mut header)])?;
        let frame_number: u32 = u32::from_le_bytes(header[0..4].try_into().unwrap());
        let data_len_bytes: usize = u32::from_le_bytes(header[4..8].try_into().unwrap()) as usize;
        if frame_number != self.console_next_frame_number.get()
            || data_len_bytes > SpiConsoleDevice::SPI_MAX_DATA_LENGTH
        {
            // This frame is junk, so we do not read the data.
            return Ok(0);
        }
        self.console_next_frame_number.set(frame_number + 1);

        // Read the SPI console frame data.
        let data_len_bytes_w_pad = (data_len_bytes + 3) & !3;
        let mut data = vec![0u8; data_len_bytes_w_pad];
        self.spi
            .run_transaction(&mut [Transfer::Write(&[0xff; 4]), Transfer::Read(&mut data)])?;

        // Copy data to the internal data queue.
        self.rx_buf.borrow_mut().extend(&data[..data_len_bytes]);
        Ok(data_len_bytes)
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
}
