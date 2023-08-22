// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use sha2::{Digest, Sha256};
use std::time::Duration;
use thiserror::Error;
use zerocopy::AsBytes;

use crate::app::TransportWrapper;
use crate::bootstrap::{Bootstrap, BootstrapOptions, UpdateProtocol};
use crate::impl_serializable_error;
use crate::io::spi::Transfer;
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
    const EOF: u32 = 0x8000_0000;
    const FLASH_SECTOR_SIZE: usize = 2048;
    const FLASH_SECTOR_MASK: usize = Self::FLASH_SECTOR_SIZE - 1;
    const FLASH_BUFFER_SIZE: usize = 128;
    const FLASH_BUFFER_MASK: usize = Self::FLASH_BUFFER_SIZE - 1;
    const DATA_LEN: usize = 2048 - std::mem::size_of::<FrameHeader>();
    const HASH_LEN: usize = 32;
    const FLASH_BASE_ADDRESS: usize = 65536 * 8;

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
    fn from_payload(payload: &[u8]) -> Vec<Frame> {
        let mut frames = Vec::new();

        let max_addr = (payload.chunks(4).rposition(|c| c != [0xff; 4]).unwrap_or(0) + 1) * 4;

        let mut frame_num = 0;
        let mut addr = 0;
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
                    flash_offset: (addr + Self::FLASH_BASE_ADDRESS) as u32,
                    ..Default::default()
                },
                ..Default::default()
            };
            let slice_size = Self::DATA_LEN.min(payload.len() - addr);
            frame.data[..slice_size].copy_from_slice(&payload[addr..addr + slice_size]);
            frames.push(frame);

            addr += Self::DATA_LEN;
            frame_num += 1;
        }
        if let Some(f) = frames.last_mut() {
            f.header.frame_num |= Self::EOF;
        }
        frames
            .iter_mut()
            .for_each(|f| f.header.hash = f.header_hash());
        frames
    }
}

/// Implements the bootstrap protocol of previous Google Titan family chips.
pub struct Legacy {
    /// Controls the time that CS is deasserted between frames.  With Dauntless, 20ms has been
    /// observed to be "too long", in that after the final frame was transmitted, the bootloader
    /// could have already stopped listening to SPI and started booting the newly flashed code,
    /// before OpenTitan tool could read the ACK of the final transaction.  1ms is what the
    /// spiflash.cc tool from cr50-utils uses.
    pub inter_frame_delay: Duration,
}

impl Legacy {
    const INTER_FRAME_DELAY: Duration = Duration::from_millis(1);
    const MAX_CONSECUTIVE_ERRORS: u32 = 100;

    /// Creates a new `Primitive` protocol updater from `options`.
    pub fn new(options: &BootstrapOptions) -> Self {
        Self {
            inter_frame_delay: options.inter_frame_delay.unwrap_or(Self::INTER_FRAME_DELAY),
        }
    }
}

#[derive(Debug, Error, serde::Serialize, serde::Deserialize)]
pub enum LegacyBootstrapError {
    #[error("Boot rom not ready")]
    NotReady,
    #[error("Unknown boot rom error: {0}")]
    Unknown(u8),
    #[error("Boot rom error: NOREQUEST")]
    NoRequest,
    #[error("Boot rom error: NOMAGIC")]
    NoMagic,
    #[error("Boot rom error: TOOBIG")]
    TooBig,
    #[error("Boot rom error: TOOHIGH")]
    TooHigh,
    #[error("Boot rom error: NOALIGN")]
    NoAlign,
    #[error("Boot rom error: NOROUND")]
    NoRound,
    #[error("Boot rom error: BADKEY")]
    BadKey,
    #[error("Boot rom error: BADSTART")]
    BadStart,
    #[error("Boot rom error: NOWIPE")]
    NoWipe,
    #[error("Boot rom error: NOWIPE0")]
    NoWipe0,
    #[error("Boot rom error: NOWIPE1")]
    NoWipe1,
    #[error("Boot rom error: NOTEMPTY")]
    NotEmpty,
    #[error("Boot rom error: NOWRITE")]
    NoWrite,
    #[error("Boot rom error: BADADR")]
    BadAdr,
    #[error("Boot rom error: OVERFLOW")]
    Overflow,
    #[error("Repeated errors communicating with boot rom")]
    RepeatedErrors,
}
impl_serializable_error!(LegacyBootstrapError);

impl From<u8> for LegacyBootstrapError {
    fn from(value: u8) -> LegacyBootstrapError {
        match value {
            // All zeroes or all ones means that the bootloader is not yet ready to respond.
            0 | 255 => LegacyBootstrapError::NotReady,
            // Other values represent particular errors.
            1 => LegacyBootstrapError::NoRequest,
            2 => LegacyBootstrapError::NoMagic,
            3 => LegacyBootstrapError::TooBig,
            4 => LegacyBootstrapError::TooHigh,
            5 => LegacyBootstrapError::NoAlign,
            6 => LegacyBootstrapError::NoRound,
            7 => LegacyBootstrapError::BadKey,
            8 => LegacyBootstrapError::BadStart,
            10 => LegacyBootstrapError::NoWipe,
            11 => LegacyBootstrapError::NoWipe0,
            12 => LegacyBootstrapError::NoWipe1,
            13 => LegacyBootstrapError::NotEmpty,
            14 => LegacyBootstrapError::NoWrite,
            15 => LegacyBootstrapError::BadAdr,
            16 => LegacyBootstrapError::Overflow,
            n => LegacyBootstrapError::Unknown(n),
        }
    }
}

impl UpdateProtocol for Legacy {
    fn verify_capabilities(
        &self,
        _container: &Bootstrap,
        transport: &TransportWrapper,
    ) -> Result<()> {
        transport
            .capabilities()?
            .request(Capability::GPIO | Capability::SPI)
            .ok()?;
        Ok(())
    }

    fn uses_common_bootstrap_reset(&self) -> bool {
        true
    }

    /// Performs the update protocol using the `transport` with the firmware `payload`.
    fn update(
        &self,
        container: &Bootstrap,
        transport: &TransportWrapper,
        payload: &[u8],
        progress: &dyn ProgressIndicator,
    ) -> Result<()> {
        let spi = container.spi_params.create(transport, "BOOTSTRAP")?;

        let frames = Frame::from_payload(payload);

        // All frames up to but not including this index have been ack'ed by the bootloader.
        // Once this reaches frames.len(), the operation was successful.
        let mut first_unacked_index = 0;

        // Counts the number of repeated failures in getting a frame ack.
        let mut consecutive_errors = 0;

        // Set if the past transaction ack'ed the block sent before that one, while transmitting
        // the next.  If so, we heuristically assume that the block just sent will be ack'ed in
        // the upcoming bidirectional transaction.
        let mut optimistic = false;

        // Set if the past transaction ack'ed the block sent before that one, while
        // re-transmitting the same block.  If so, we do not care about the ack in the upcoming
        // bidirectional transaction, as it turns out it was not necessary to perform the most
        // recent re-transmission.
        let mut becoming_optimistic = false;

        progress.new_stage("", payload.len());
        loop {
            if consecutive_errors > Self::MAX_CONSECUTIVE_ERRORS {
                return Err(LegacyBootstrapError::RepeatedErrors.into());
            }

            let second_unacked_index = (first_unacked_index + 1).min(frames.len() - 1);
            let transmit_index = if optimistic {
                second_unacked_index
            } else {
                first_unacked_index
            };
            let frame = &frames[transmit_index];
            eprint!("{}.", transmit_index);
            std::thread::sleep(self.inter_frame_delay);

            // Write the frame and read back the ack of a previously transmitted frame.
            progress.progress(frame.header.flash_offset as usize - Frame::FLASH_BASE_ADDRESS);
            let mut response = [0u8; std::mem::size_of::<Frame>()];
            spi.run_transaction(&mut [Transfer::Both(frame.as_bytes(), &mut response)])?;

            if becoming_optimistic {
                optimistic = true;
                becoming_optimistic = false;
                continue;
            }

            if response[..Frame::HASH_LEN]
                .iter()
                .all(|&x| x == response[0])
            {
                // A response consisteing of all identical bytes is a status code.
                match LegacyBootstrapError::from(response[0]) {
                    LegacyBootstrapError::NotReady => {
                        consecutive_errors += 1;
                        continue; // Retry sending same frame.
                    }
                    error => return Err(error.into()),
                }
            }

            if response[..Frame::HASH_LEN] == frames[first_unacked_index].frame_hash() {
                first_unacked_index += 1;
            } else if response[..Frame::HASH_LEN] == frames[second_unacked_index].frame_hash() {
                first_unacked_index = second_unacked_index + 1;
            } else {
                consecutive_errors += 1;
                optimistic = false;
                continue;
            }

            consecutive_errors = 0;
            if first_unacked_index == frames.len() {
                // All frames acked, we are done.
                break;
            }
            if !optimistic {
                // Heuristic, become optimistic after second or later frame is ack'ed.
                becoming_optimistic = first_unacked_index > 1;
            }
        }
        progress.progress(payload.len());
        eprintln!("success");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SIMPLE_BIN: &[u8; 2048] = include_bytes!("simple.bin");

    #[test]
    fn test_small_binary() -> Result<()> {
        let frames = Frame::from_payload(SIMPLE_BIN);

        assert_eq!(frames[0].header.frame_num, 0);
        assert_eq!(frames[0].header.flash_offset, 0x80000);
        assert_eq!(
            hex::encode(frames[0].header.hash),
            "4e31bfd8b3be32358f2235c0f241f3970de575fc6aca0564aa6bf30adaf33910"
        );

        assert_eq!(frames[1].header.frame_num, 0x8000_0001);
        assert_eq!(frames[1].header.flash_offset, 0x807d8);
        assert_eq!(
            hex::encode(frames[1].header.hash),
            "ff584c07bbb0a039934a660bd49b7812af8ee847d1e675d9aba71c11fab3cfcb"
        );
        Ok(())
    }
}
