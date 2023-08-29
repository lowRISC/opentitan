// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use sha2::{Digest, Sha256};
use std::time::{Duration, Instant};
use thiserror::Error;
use zerocopy::AsBytes;

use crate::app::TransportWrapper;
use crate::bootstrap::{Bootstrap, BootstrapOptions, UpdateProtocol};
use crate::impl_serializable_error;
use crate::io::uart::Uart;
use crate::transport::{Capability, ProgressIndicator};

#[derive(AsBytes, Debug, Default)]
#[repr(C)]
struct FrameHeader {
    hash: [u8; Frame::HASH_LEN],
    frame_num: u32,
    flash_offset: u32,
}

#[derive(AsBytes, Debug)]
#[repr(C)]
struct Frame {
    header: FrameHeader,
    data: [u8; Frame::DATA_LEN],
}

impl Default for Frame {
    fn default() -> Self {
        Frame {
            header: Default::default(),
            data: [0xff; Frame::DATA_LEN],
        }
    }
}

impl Frame {
    const FLASH_SECTOR_SIZE: usize = 2048;
    const FLASH_SECTOR_MASK: usize = Self::FLASH_SECTOR_SIZE - 1;
    const FLASH_BUFFER_SIZE: usize = 128;
    const FLASH_BUFFER_MASK: usize = Self::FLASH_BUFFER_SIZE - 1;
    const DATA_LEN: usize = 1024 - std::mem::size_of::<FrameHeader>();
    const HASH_LEN: usize = 32;
    const HEADER_ALIGNMENT: usize = 0x1000;
    const GSC_FLASH_MEMMAP_OFFSET: usize = 0x80000;
    const GSC_HEADER_LENGTH_FIELD_OFFSET: usize = 0x338;
    const MAGIC_HEADER: [u8; 4] = [0xfd, 0xff, 0xff, 0xff];
    const CRYPTOLIB_TELL: [u8; 4] = [0x53, 0x53, 0x53, 0x53];

    /// Computes the hash in the header.
    fn header_hash(&self) -> [u8; Frame::HASH_LEN] {
        let frame = self.as_bytes();
        let sha = Sha256::digest(&frame[Frame::HASH_LEN..]);
        sha.into()
    }

    /// Computes the hash over the entire frame.
    fn frame_hash(&self) -> [u8; Frame::HASH_LEN] {
        let mut digest = Sha256::digest(self.as_bytes());
        // Touch up zeroes into ones, as that is what the old chips are doing.
        for b in &mut digest {
            if *b == 0 {
                *b = 1;
            }
        }
        digest.into()
    }

    /// Creates a sequence of frames based on a `payload` binary.
    fn from_payload(payload: &[u8]) -> Result<Vec<Frame>> {
        // The given payload will contain up to four sections concatenated together:
        // RO_A, RW_A optionally follwed by RO_B, RW_B
        // Each section starts with a magic number on at least a 256 byte boundary.

        // This rescue protocol uses the RW_A section only, which will start at the second
        // occurrance of the magic value, and end at the third occurrence or at the end of the
        // file.

        ensure!(
            payload.starts_with(&Self::MAGIC_HEADER),
            RescueError::ImageFormatError
        );

        // Find second occurrence of magic value, not followed by signature of encrypted
        // cryptolib, this will be the header of RW in slot A.
        let min_addr = match payload[Self::HEADER_ALIGNMENT..]
            .chunks(Self::HEADER_ALIGNMENT)
            .position(|c| c[0..4] == Self::MAGIC_HEADER && c[4..8] != Self::CRYPTOLIB_TELL)
        {
            Some(n) => (n + 1) * Self::HEADER_ALIGNMENT,
            None => bail!(RescueError::ImageFormatError),
        };

        // Inspect the length field of the RW header.
        let length_field_at = min_addr + Self::GSC_HEADER_LENGTH_FIELD_OFFSET;
        let max_addr = u32::from_le_bytes(payload[length_field_at..length_field_at + 4].try_into()?)
            as usize
            - Self::GSC_FLASH_MEMMAP_OFFSET;

        // Trim trailing 0xff bytes.
        let max_addr = (payload[..max_addr]
            .chunks(4)
            .rposition(|c| c != [0xff; 4])
            .unwrap_or(0)
            + 1)
            * 4;

        // Round up to multiple of 128 bytes, this is to ensure that the bootloader flushes the
        // last data transmitted, even in the absense of the "EOF" flag.  The reason we do not
        // send that flag is that it causes immediate boot into the code just programmed, and we
        // want to allow the user to use --leave_in_reset to control exactly when the newly
        // programmed code should first run.
        let max_addr = (max_addr + Self::FLASH_BUFFER_SIZE - 1) & !Self::FLASH_BUFFER_MASK;

        let mut frames = Vec::new();
        let mut frame_num = 0;
        let mut addr = min_addr;
        while addr < max_addr {
            // Try skipping over 0xffffffff words.
            let nonempty_addr = addr
                + payload[addr..]
                    .chunks(4)
                    .position(|c| c != [0xff; 4])
                    .unwrap()
                    * 4;
            let skip_addr = nonempty_addr & !Self::FLASH_SECTOR_MASK;
            if skip_addr > addr && (addr == 0 || addr & Self::FLASH_BUFFER_MASK != 0) {
                // Can only skip from the start or if the last addr wasn't an exact multiple of
                // 128 (per H1D boot rom).
                addr = skip_addr;
            }

            let mut frame = Frame {
                header: FrameHeader {
                    frame_num,
                    flash_offset: addr as u32,
                    ..Default::default()
                },
                ..Default::default()
            };
            let slice_size = Self::DATA_LEN.min(max_addr - addr);
            frame.data[..slice_size].copy_from_slice(&payload[addr..addr + slice_size]);
            for i in slice_size..Self::DATA_LEN {
                frame.data[i] = 0xFF;
            }
            frames.push(frame);

            addr += Self::DATA_LEN;
            frame_num += 1;
        }
        frames
            .iter_mut()
            .for_each(|f| f.header.hash = f.header_hash());
        Ok(frames)
    }
}

#[derive(Debug, Error, serde::Serialize, serde::Deserialize)]
pub enum RescueError {
    #[error("Unrecognized image file format")]
    ImageFormatError,
    #[error("Synchronization error communicating with boot rom")]
    SyncError,
    #[error("Repeated errors communicating with boot rom")]
    RepeatedErrors,
}
impl_serializable_error!(RescueError);

/// Implements the UART rescue protocol of Google Ti50 firmware.
pub struct Rescue {}

impl Rescue {
    /// Abort if a block has not been accepted after this number of retries.
    const MAX_CONSECUTIVE_ERRORS: u32 = 50;
    /// Take some measure to regain protocol synchronization, in case of this number of retries
    /// of the same block.
    const RESYNC_AFTER_CONSECUTIVE_ERRORS: u32 = 3;

    /// Creates a new `Rescue` protocol updater from `options`.
    pub fn new(_options: &BootstrapOptions) -> Self {
        Self {}
    }

    /// Waits for some time for a character, returns None on timeout.
    fn read_char(&self, uart: &dyn Uart) -> Option<char> {
        let mut buf = [0u8; 1];
        match uart.read_timeout(&mut buf, Duration::from_millis(100)) {
            Ok(1) => Some(buf[0] as char),
            Ok(_) => None,
            _ => None,
        }
    }

    /// Waits some time for data, returning true if the given string was seen in full, or false
    /// as soon as a non-matching character is received or on timeout.
    fn expect_string(&self, uart: &dyn Uart, s: &str) -> bool {
        for expected_ch in s.chars() {
            match self.read_char(uart) {
                Some(ch) if ch == expected_ch => (),
                _ => return false,
            }
        }
        true
    }

    /// Reads and discards any characters in the receive buffer, waiting a little while for any
    /// more which will also be discarded.
    fn flush_rx(&self, uart: &dyn Uart, timeout: Duration) {
        let mut response = [0u8; Frame::HASH_LEN];
        loop {
            match uart.read_timeout(&mut response, timeout) {
                Ok(0) | Err(_) => break,
                Ok(_) => continue,
            }
        }
    }

    /// As the 1024 byte blocks sent to the chip have no discernible header, the sender and
    /// receiver could be "out of sync".  This is resolved by sending one byte at a time, and
    /// observing when the chip sends a response (which will be a rejection due to checksum).
    fn synchronize(&self, uart: &dyn Uart) -> Result<()> {
        // Most likely, only a few "extra" bytes have been sent during initial negotiation.
        // Send almost a complete block in one go, and then send each of the last 16 bytes one
        // at a time, slowly enough to detect a response before sending the next byte.
        uart.write(&[0u8; 1008])?;
        let mut response = [0u8; 1];
        let limit = match uart.read_timeout(&mut response, Duration::from_millis(50)) {
            Ok(0) | Err(_) => 16,
            Ok(_) => {
                // A response at this point must mean that more than 16 bytes had already been
                // sent before entering this method.  This will be resolved by doing another
                // slower round of 1024 bytes with delay in between every one.
                self.flush_rx(uart, Duration::from_millis(500));
                1024
            }
        };
        for _ in 0..limit {
            uart.write(&[0u8; 1])?;
            match uart.read_timeout(&mut response, Duration::from_millis(50)) {
                Ok(0) | Err(_) => (),
                Ok(_) => {
                    self.flush_rx(uart, Duration::from_millis(500));
                    return Ok(());
                }
            }
        }
        Err(RescueError::SyncError.into())
    }

    /// Reset the chip and send the magic 'r' character at the opportune moment during boot in
    /// order to enter rescue more, repeat if necessary.
    fn enter_rescue_mode(&self, container: &Bootstrap, uart: &dyn Uart) -> Result<()> {
        // Attempt getting the attention of the bootloader.
        let timeout = Duration::from_millis(2000);
        for _ in 0..Self::MAX_CONSECUTIVE_ERRORS {
            eprint!("Resetting...");
            container.reset_pin.write(false)?; // Low active
            uart.write(&[3])?; // Send a character to ensure that HyperDebug UART->USB
                               // forwarding has "woken up", see issue #19564.
            self.flush_rx(uart, container.reset_delay);
            container.reset_pin.write(true)?; // Release reset

            let stopwatch = Instant::now();
            while stopwatch.elapsed() < timeout {
                if !self.expect_string(uart, "Bldr |") {
                    continue;
                }
                uart.write(b"r")?;
                eprint!("a.");
                while stopwatch.elapsed() < timeout {
                    if !self.expect_string(uart, "oops?|") {
                        continue;
                    }
                    uart.write(b"r")?;
                    eprint!("b.");
                    if self.expect_string(uart, "escue") {
                        eprintln!("c: Entered rescue mode!");
                        self.synchronize(uart)?;
                        return Ok(());
                    }
                }
            }
            eprintln!(" Failed to enter rescue mode.");
        }
        Err(RescueError::RepeatedErrors.into())
    }
}

impl UpdateProtocol for Rescue {
    fn verify_capabilities(
        &self,
        _container: &Bootstrap,
        transport: &TransportWrapper,
    ) -> Result<()> {
        transport
            .capabilities()?
            .request(Capability::GPIO | Capability::UART)
            .ok()?;
        Ok(())
    }

    /// Returns false, in order to as the containing Bootstrap struct to not perform standard
    /// BOOTSTRAP/RESET sequence.
    fn uses_common_bootstrap_reset(&self) -> bool {
        false
    }

    /// Performs the update protocol using the `transport` with the firmware `payload`.
    fn update(
        &self,
        container: &Bootstrap,
        transport: &TransportWrapper,
        payload: &[u8],
        progress: &dyn ProgressIndicator,
    ) -> Result<()> {
        let frames = Frame::from_payload(payload)?;
        let uart = container.uart_params.create(transport)?;

        self.enter_rescue_mode(container, &*uart)?;

        // Send frames one at a time.
        progress.new_stage("", frames.len() * Frame::DATA_LEN);
        'next_block: for (idx, frame) in frames.iter().enumerate() {
            for consecutive_errors in 0..Self::MAX_CONSECUTIVE_ERRORS {
                eprint!("{}.", idx);
                progress.progress(idx * Frame::DATA_LEN);
                uart.write(frame.as_bytes())?;
                let mut response = [0u8; Frame::HASH_LEN];
                let mut index = 0;
                while index < Frame::HASH_LEN {
                    let timeout = if index == 0 {
                        Duration::from_millis(1000)
                    } else {
                        Duration::from_millis(10)
                    };
                    match uart.read_timeout(&mut response[index..], timeout) {
                        Ok(0) | Err(_) => break,
                        Ok(n) => index += n,
                    }
                }
                if index < Frame::HASH_LEN {
                    eprint!("sync.");
                    self.synchronize(&*uart)?;
                    continue;
                }
                if response[4..].chunks(4).all(|x| x == &response[..4]) {
                    eprint!("sync.");
                    self.synchronize(&*uart)?;
                } else if response == frame.frame_hash() {
                    continue 'next_block;
                } else {
                    self.flush_rx(&*uart, Duration::from_millis(500));
                    if consecutive_errors >= Self::RESYNC_AFTER_CONSECUTIVE_ERRORS {
                        eprint!("sync.");
                        self.synchronize(&*uart)?;
                    }
                }
            }
            bail!(RescueError::RepeatedErrors);
        }

        // Reset, in order to leave rescue mode.
        container.reset_pin.write(false)?; // Low active
        if !container.leave_in_reset {
            std::thread::sleep(container.reset_delay);
            container.reset_pin.write(true)?; // Release reset
        }
        progress.progress(frames.len() * Frame::DATA_LEN);
        eprintln!("Success!");
        Ok(())
    }
}
