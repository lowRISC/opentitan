// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use memoffset::offset_of;
use std::convert::TryInto;
use std::fs::File;
use std::io::{Read, Write};
use std::mem::size_of;
use std::path::{Path, PathBuf};
use thiserror::Error;

use zerocopy::LayoutVerified;

use crate::crypto::rsa::Modulus;
use crate::crypto::rsa::Signature as RsaSignature;
use crate::crypto::sha256;
use crate::crypto::spx::Signature as SpxSignature;
use crate::crypto::spx::SpxPublicKeyPart;
use crate::image::manifest::Manifest;
use crate::image::manifest_def::{
    ManifestRsaBuffer, ManifestSpec, ManifestSpxKey, ManifestSpxSignature,
};
use crate::util::file::{FromReader, ToWriter};
use crate::util::parse_int::ParseInt;

#[derive(Debug, Error)]
pub enum ImageError {
    #[error("Incomplete read: expected to read {0} bytes but read {1} bytes")]
    IncompleteRead(usize, usize),
    #[error("Failed to parse image manifest.")]
    Parse,
}

/// A buffer with the same alignment as `Manifest` for storing image data.
#[repr(C)]
#[derive(Debug)]
pub struct ImageData {
    pub bytes: [u8; Image::MAX_SIZE],
    _align: [Manifest; 0],
}

impl Default for ImageData {
    fn default() -> Self {
        ImageData {
            bytes: [0xFF; Image::MAX_SIZE],
            _align: [],
        }
    }
}

#[derive(Debug, Default)]
pub struct Image {
    data: Box<ImageData>,
    size: usize,
}

#[derive(Debug)]
pub enum ImageChunk {
    Concat(PathBuf),
    Offset(PathBuf, usize),
}

#[derive(Debug, Default)]
pub struct ImageAssembler {
    pub size: usize,
    pub mirrored: bool,
    pub chunks: Vec<ImageChunk>,
}

impl FromReader for Image {
    /// Reads in an `Image`.
    fn from_reader(mut r: impl Read) -> Result<Self> {
        let mut image = Image::default();
        image.size = r.read(&mut image.data.bytes)?;
        Ok(image)
    }
}

impl ToWriter for Image {
    /// Writes out the `Image`.
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        w.write_all(&self.data.bytes[..self.size])?;
        Ok(())
    }
}

impl Image {
    const MAX_SIZE: usize = 512 * 1024;
    /// Overwrites all fields in the image's manifest that are defined in `other`.
    pub fn overwrite_manifest(&mut self, other: ManifestSpec) -> Result<()> {
        let manifest = self.borrow_manifest_mut()?;
        let mut manifest_def: ManifestSpec = (&*manifest).try_into()?;
        manifest_def.overwrite_fields(other);
        *manifest = manifest_def.try_into()?;
        Ok(())
    }

    /// Updates the rsa_signature field in the `Manifest`.
    pub fn update_rsa_signature(&mut self, signature: RsaSignature) -> Result<()> {
        let manifest = self.borrow_manifest_mut()?;

        // Convert to a `ManifestSpec` so we can supply the signature as a `BigInt`.
        let mut manifest_def: ManifestSpec = (&*manifest).try_into()?;
        manifest_def
            .update_rsa_signature(ManifestRsaBuffer::from_le_bytes(signature.to_le_bytes())?);
        *manifest = manifest_def.try_into()?;
        Ok(())
    }

    /// Updates the rsa_modulus field in the `Manifest`.
    pub fn update_modulus(&mut self, rsa_modulus: Modulus) -> Result<()> {
        let manifest = self.borrow_manifest_mut()?;

        // Convert to a `ManifestSpec` so we can supply the rsa_modulus as a `BigInt`.
        let mut manifest_def: ManifestSpec = (&*manifest).try_into()?;
        manifest_def.update_modulus(ManifestRsaBuffer::from_le_bytes(rsa_modulus.to_le_bytes())?);
        *manifest = manifest_def.try_into()?;
        Ok(())
    }

    /// Updates the spx_signature field in the `Manifest`.
    pub fn update_spx_signature(&mut self, signature: SpxSignature) -> Result<()> {
        let manifest = self.borrow_manifest_mut()?;

        let mut manifest_def: ManifestSpec = (&*manifest).try_into()?;
        manifest_def.update_spx_signature(ManifestSpxSignature::from_le_bytes(
            signature.to_le_bytes(),
        )?);

        *manifest = manifest_def.try_into()?;
        Ok(())
    }

    /// Updates the spx_key field in the `Manifest`.
    pub fn update_spx_key(&mut self, key: &impl SpxPublicKeyPart) -> Result<()> {
        let manifest = self.borrow_manifest_mut()?;

        let mut manifest_def: ManifestSpec = (&*manifest).try_into()?;
        manifest_def.update_spx_key(ManifestSpxKey::from_le_bytes(key.pk_as_bytes())?);

        *manifest = manifest_def.try_into()?;
        Ok(())
    }

    pub fn borrow_manifest(&self) -> Result<&Manifest> {
        let manifest_slice = &self.data.bytes[0..size_of::<Manifest>()];
        let manifest_layout: LayoutVerified<&[u8], Manifest> =
            LayoutVerified::new(manifest_slice).ok_or(ImageError::Parse)?;
        let manifest: &Manifest = manifest_layout.into_ref();
        Ok(manifest)
    }

    pub fn borrow_manifest_mut(&mut self) -> Result<&mut Manifest> {
        let manifest_slice = &mut self.data.bytes[0..size_of::<Manifest>()];
        let manifest_layout: LayoutVerified<&mut [u8], Manifest> =
            LayoutVerified::new(&mut *manifest_slice).ok_or(ImageError::Parse)?;
        let manifest: &mut Manifest = manifest_layout.into_mut();
        Ok(manifest)
    }

    /// Updates the length field in the `Manifest` to the length of the image.
    pub fn update_length(&mut self) -> Result<usize> {
        let length = self.size as u32;
        let m = self.borrow_manifest_mut()?;
        m.length = length;
        Ok(self.size)
    }

    /// Updates the `signed_reion_end` field
    pub fn update_signed_region(&mut self) -> Result<usize> {
        // TODO(#18496): Should depend on extensions.
        let signed_region_end = self.size as u32;
        let m = self.borrow_manifest_mut()?;
        m.signed_region_end = signed_region_end;
        Ok(self.size)
    }

    /// Operates on the signed region of the image.
    pub fn map_signed_region<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[u8]) -> R,
    {
        f(&self.data.bytes[offset_of!(Manifest, usage_constraints)..self.size])
    }

    /// Compute the SHA256 digest for the signed portion of the `Image`.
    pub fn compute_digest(&self) -> sha256::Sha256Digest {
        self.map_signed_region(|v| sha256::sha256(v))
    }
}

impl ImageAssembler {
    /// Creates an `ImageAssembler` with a given `size` and mirroring parameters.
    pub fn with_params(size: usize, mirrored: bool) -> Self {
        ImageAssembler {
            size,
            mirrored,
            ..Default::default()
        }
    }

    /// Creates an `ImageAssembler` with default parameters for OpenTitan: a 1MiB image which is mirrored.
    pub fn new() -> Self {
        Self::with_params(0x100000, true)
    }

    /// Parse a list of strings into chunks to be assembled.
    /// Each string may be a filename or a filename@offset describing where in the assembled image the contents of the file should appear.
    /// The offset is an integer expressed in any of the bases accepted by [`ParseInt`].
    pub fn parse(&mut self, chunks: &[impl AsRef<str>]) -> Result<()> {
        for chunk in chunks {
            if let Some((file, offset)) = chunk.as_ref().split_once('@') {
                self.chunks.push(ImageChunk::Offset(
                    PathBuf::from(file),
                    usize::from_str(offset)?,
                ));
            } else {
                self.chunks
                    .push(ImageChunk::Concat(PathBuf::from(chunk.as_ref())));
            }
        }
        Ok(())
    }

    // Read a file into a buffer.  Ensure the entire file is read.
    fn read(path: &Path, buf: &mut [u8]) -> Result<usize> {
        let mut file = File::open(path)?;
        let len = file.metadata()?.len() as usize;
        let n = file.read(buf)?;
        ensure!(len == n, ImageError::IncompleteRead(len, n));
        Ok(n)
    }

    /// Assemble the image according to the parameters and parsed chunk specifications.
    pub fn assemble(&self) -> Result<Vec<u8>> {
        let size = if self.mirrored {
            self.size / 2
        } else {
            self.size
        };
        let mut image = vec![0xff; size];
        let mut pos = 0;
        for chunk in &self.chunks {
            match chunk {
                ImageChunk::Concat(path) => {
                    let n = Self::read(path, &mut image[pos..])?;
                    pos += n;
                }
                ImageChunk::Offset(path, offset) => {
                    let n = Self::read(path, &mut image[*offset..])?;
                    pos = offset + n;
                }
            }
        }
        if self.mirrored {
            image.extend_from_within(..size);
        }
        Ok(image)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;

    #[test]
    fn test_assemble_concat() -> Result<()> {
        // Test image assembly by concatenation.
        let mut image = ImageAssembler::with_params(16, false);
        image.parse(&[
            testdata!("hello.txt").to_str().unwrap(),
            testdata!("world.txt").to_str().unwrap(),
        ])?;
        let data = image.assemble()?;
        assert_eq!(data, b"HelloWorld\xff\xff\xff\xff\xff\xff");
        Ok(())
    }

    #[test]
    fn test_assemble_offset() -> Result<()> {
        // Test image assembly by explicit offsets.
        let mut image = ImageAssembler::with_params(16, false);
        image.parse(&[
            testdata!("hello.txt@0").to_str().unwrap(),
            testdata!("world.txt@0x8").to_str().unwrap(),
        ])?;
        let data = image.assemble()?;
        assert_eq!(data, b"Hello\xff\xff\xffWorld\xff\xff\xff");
        Ok(())
    }

    #[test]
    fn test_assemble_mirrored() -> Result<()> {
        // Test image assembly with mirroring.
        let mut image = ImageAssembler::with_params(20, true);
        image.parse(&[
            testdata!("hello.txt").to_str().unwrap(),
            testdata!("world.txt").to_str().unwrap(),
        ])?;
        let data = image.assemble()?;
        assert_eq!(data, b"HelloWorldHelloWorld");
        Ok(())
    }

    #[test]
    fn test_assemble_mirrored_offset_error() -> Result<()> {
        // Test image assembly where one of the source files isn't read completely.
        let mut image = ImageAssembler::with_params(16, true);
        image.parse(&[
            testdata!("hello.txt@0").to_str().unwrap(),
            testdata!("world.txt@0x5").to_str().unwrap(),
        ])?;
        let err = image.assemble().unwrap_err();
        assert_eq!(
            err.to_string(),
            "Incomplete read: expected to read 5 bytes but read 3 bytes"
        );
        Ok(())
    }

    #[test]
    fn test_load_image() {
        // Read and write back image.
        let image = Image::read_from_file(&testdata!("test_image.bin")).unwrap();
        image
            .write_to_file(&testdata!("test_image_out.bin"))
            .unwrap();

        // Ensure the result is identical to the original.
        let (mut orig_bytes, mut res_bytes) = (Vec::<u8>::new(), Vec::<u8>::new());
        File::open(testdata!("test_image.bin"))
            .unwrap()
            .read_to_end(&mut orig_bytes)
            .unwrap();
        File::open(testdata!("test_image_out.bin"))
            .unwrap()
            .read_to_end(&mut res_bytes)
            .unwrap();
        assert_eq!(orig_bytes, res_bytes);
    }
}
