// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings)]
#![deny(unused)]
#![deny(unsafe_code)]

use std::mem::size_of;
use std::ops::Deref;
use std::ops::DerefMut;

use thiserror::Error;
use zerocopy::AsBytes;
use zerocopy::LayoutVerified;

use crate::manifest::Manifest;

#[derive(Error, Debug, PartialEq)]
pub enum ImageError {
    #[error("Failed to parse image manifest.")]
    Parse,
}

/// A thin wrapper around manifest and payload buffers to help with setting manifest fields and
/// signing the image.
#[derive(Debug)]
pub struct Image<'a> {
    pub manifest: LayoutVerified<&'a mut [u8], Manifest>,
    pub payload: &'a [u8],
}

impl<'a> Image<'a> {
    pub fn new(
        manifest_buffer: &'a mut ManifestBuffer,
        payload: &'a [u8],
    ) -> Result<Image<'a>, ImageError> {
        let manifest = LayoutVerified::new(&mut **manifest_buffer).ok_or(ImageError::Parse)?;
        Ok(Self { manifest, payload })
    }

    pub fn bytes(&self) -> Vec<u8> {
        [self.manifest.as_bytes(), self.payload].concat()
    }

    pub fn signed_bytes(&self) -> Vec<u8> {
        self.bytes()
            .split_off(self.manifest.signature.as_bytes().len())
    }
}

/// A buffer with the same size and alignment as `Manifest`.
pub struct ManifestBuffer {
    buf: [u8; size_of::<Manifest>()],
    // This forces this struct to have the same alignment as `Manifest`.
    _align: [Manifest; 0],
}

impl ManifestBuffer {
    pub fn new() -> Self {
        Self {
            buf: [0u8; size_of::<Manifest>()],
            _align: [],
        }
    }
}

impl Default for ManifestBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for ManifestBuffer {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.buf
    }
}

impl DerefMut for ManifestBuffer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.buf
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use memoffset::offset_of;

    #[test]
    fn test_set_manifest_field() -> Result<(), ImageError> {
        let mut manifest_buffer = ManifestBuffer::new();
        let payload = [0u8; 0];
        let mut image = Image::new(&mut manifest_buffer, &payload)?;
        let identifier: u32 = 0x01020304;
        image.manifest.identifier = identifier;
        for i in 0..4 {
            assert_eq!(
                manifest_buffer[offset_of!(Manifest, identifier) + i],
                identifier.to_le_bytes()[i]
            );
        }
        Ok(())
    }

    #[test]
    fn test_bytes() -> Result<(), ImageError> {
        let mut manifest_buffer = ManifestBuffer::new();
        let payload = [5u8, 6u8, 7u8, 8u8];
        let mut image = Image::new(&mut manifest_buffer, &payload)?;
        let identifier: u32 = 0x01020304;
        image.manifest.identifier = identifier;
        let bytes = image.bytes();
        for i in 0..4 {
            assert_eq!(bytes[i], manifest_buffer[i]);
            assert_eq!(bytes[size_of::<Manifest>() + i], payload[i]);
        }
        Ok(())
    }
}
