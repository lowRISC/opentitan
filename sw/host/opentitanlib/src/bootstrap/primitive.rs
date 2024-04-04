// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use sha2::{Digest, Sha256};
use std::time::Duration;
use zerocopy::AsBytes;

use crate::app::TransportWrapper;
use crate::bootstrap::{Bootstrap, BootstrapOptions, UpdateProtocol};
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
    const DATA_LEN: usize = 2048 - std::mem::size_of::<FrameHeader>();
    const HASH_LEN: usize = 32;

    /// Computes the hash in the header.
    fn header_hash(&self) -> [u8; Frame::HASH_LEN] {
        let frame = self.as_bytes();
        let mut digest = Sha256::digest(&frame[Frame::HASH_LEN..]);
        // Note: the OpenTitan HMAC produces the digest in little-endian order,
        // so we reverse the order of the bytes in the digest.
        digest.reverse();
        digest.into()
    }

    /// Computes the hash over the entire frame.
    fn frame_hash(&self) -> [u8; Frame::HASH_LEN] {
        let mut digest = Sha256::digest(self.as_bytes());
        // Note: the OpenTitan HMAC produces the digest in little-endian order,
        // so we reverse the order of the bytes in the digest.
        digest.reverse();
        digest.into()
    }

    /// Creates a sequence of frames based on a `payload` binary.
    fn from_payload(payload: &[u8]) -> Vec<Frame> {
        let mut frames = Vec::new();
        let last_frame = (payload.len() + Frame::DATA_LEN - 1) / Frame::DATA_LEN - 1;
        for (i, chunk) in payload.chunks(Frame::DATA_LEN).enumerate() {
            let mut frame = Frame {
                header: FrameHeader {
                    frame_num: if i == last_frame {
                        i as u32 | Frame::EOF
                    } else {
                        i as u32
                    },
                    flash_offset: (i * Frame::DATA_LEN) as u32,
                    ..Default::default()
                },
                ..Default::default()
            };
            frame.data[..chunk.len()].copy_from_slice(chunk);
            frame.header.hash = frame.header_hash();
            frames.push(frame)
        }
        frames
    }
}

/// Implements the primitive bootstrap protocol.
pub struct Primitive {
    pub inter_frame_delay: Duration,
    pub flash_erase_delay: Duration,
}

impl Primitive {
    // Imperically, a 50ms IFD improves console itegrity and fixes bootstrap for a slower, Bazel
    // built Test ROM.
    const INTER_FRAME_DELAY: Duration = Duration::from_millis(50);
    const FLASH_ERASE_DELAY: Duration = Duration::from_millis(200);

    /// Creates a new `Primitive` protocol updater from `options`.
    pub fn new(options: &BootstrapOptions) -> Self {
        Primitive {
            inter_frame_delay: options.inter_frame_delay.unwrap_or(Self::INTER_FRAME_DELAY),
            flash_erase_delay: options.flash_erase_delay.unwrap_or(Self::FLASH_ERASE_DELAY),
        }
    }
}

impl UpdateProtocol for Primitive {
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

        progress.new_stage("", payload.len());
        let mut i = 0;
        while i < frames.len() {
            let frame = &frames[i];
            log::info!(
                "Writing frame {} (offset {:x?})",
                i,
                frame.header.flash_offset
            );

            // Write the frame and read back the hash of the previous frame.
            progress.progress(frame.header.flash_offset as usize);
            let mut prev_hash = [0u8; std::mem::size_of::<Frame>()];
            spi.run_transaction(&mut [Transfer::Both(frame.as_bytes(), &mut prev_hash)])?;

            if i == 0 {
                // If its the first frame, there is no hash to check.
                // We need to give the target some time to erase the flash.
                std::thread::sleep(self.flash_erase_delay);
                i += 1;
                continue;
            }

            std::thread::sleep(self.inter_frame_delay);
            let want_hash = frames[i - 1].frame_hash();
            if prev_hash[..Frame::HASH_LEN] != want_hash {
                log::error!(
                    "Frame hash mismatch device:{:x?} != frame:{:x?}.",
                    &prev_hash[..Frame::HASH_LEN],
                    want_hash
                );
                continue;
            }
            i += 1;
        }
        progress.progress(payload.len());
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
        assert_eq!(frames[0].header.flash_offset, 0);
        assert_eq!(
            hex::encode(frames[0].header.hash),
            "923c1347b206b78378db57198f559b66fd2822a0230b512306986f0bc6c763d2"
        );

        assert_eq!(frames[1].header.frame_num, 0x8000_0001);
        assert_eq!(frames[1].header.flash_offset, 0x7d8);
        assert_eq!(
            hex::encode(frames[1].header.hash),
            "0c79dad542f76f01c3712a051b4ef9dfd3a6e885dd9320ce3441e71016799c74"
        );
        Ok(())
    }
}
