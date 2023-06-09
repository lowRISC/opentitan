// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use memoffset::offset_of;
use std::convert::TryInto;
use std::fs::File;
use std::io::{Read, Write};
use std::mem::{align_of, size_of};
use std::path::{Path, PathBuf};
use thiserror::Error;

use zerocopy::LayoutVerified;

use crate::crypto::rsa::Modulus;
use crate::crypto::rsa::Signature as RsaSignature;
use crate::crypto::sha256;
use crate::image::manifest::{Manifest, ManifestExtHeader, ManifestExtTableEntry};
use crate::image::manifest_def::{ManifestRsaBuffer, ManifestSpec};
use crate::image::manifest_ext::{ManifestExtEntry, ManifestExtEntrySpec, ManifestExtSpec};
use crate::util::file::{FromReader, ToWriter};
use crate::util::parse_int::ParseInt;

#[derive(Debug, Error)]
pub enum ImageError {
    #[error("Incomplete read: expected to read {0} bytes but read {1} bytes")]
    IncompleteRead(usize, usize),
    #[error("Failed to parse image manifest.")]
    Parse,
    #[error("Extension data overflows flash image.")]
    ExtensionOverflow,
    #[error("Extension table index is out of bounds.")]
    BadExtensionTableIndex,
    #[error("Extension ID 0x{0:x} not in manifest table.")]
    NoExtensionTableEntry(u32),
    #[error("Extension 0x{0:x} is not aligned to word boundary.")]
    BadExtensionAlignment(u32),
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
    pub size: usize,
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
    pub const MAX_SIZE: usize = 512 * 1024;
    /// Overwrites all fields in the image's manifest that are defined in `other`.
    pub fn overwrite_manifest(&mut self, other: ManifestSpec) -> Result<()> {
        let manifest = self.borrow_manifest_mut()?;
        let mut manifest_def: ManifestSpec = (&*manifest).try_into()?;
        manifest_def.overwrite_fields(other);
        *manifest = manifest_def.try_into()?;
        Ok(())
    }

    /// Updates the data in a pre-existing extension. Does not update the image size.
    pub fn update_extension_data(&mut self, id: u32, bytes: &[u8]) -> Result<()> {
        let entry = self
            .borrow_manifest()?
            .extensions
            .entries
            .iter()
            .find(|x| x.identifier == id)
            .ok_or(ImageError::NoExtensionTableEntry(id))?;
        let offset = entry.offset as usize + std::mem::size_of::<ManifestExtHeader>();
        let extension_slice = self
            .data
            .bytes
            .get_mut(offset..offset + bytes.len())
            .ok_or(ImageError::ExtensionOverflow)?;
        extension_slice.copy_from_slice(bytes);
        Ok(())
    }

    /// Adds a new extension at the end of the image and updates size.
    /// Note that this method does NOT update the `signed_region_end` or `length` fields of the
    /// manifest.
    /// New extensions are ALWAYS added at the end of the image by design.
    pub fn add_extension_data(&mut self, bytes: &[u8]) -> Result<()> {
        let end_index = self
            .size
            .checked_add(bytes.len())
            .ok_or(ImageError::ExtensionOverflow)?;
        let extension_slice = self
            .data
            .bytes
            .get_mut(self.size..end_index)
            .ok_or(ImageError::ExtensionOverflow)?;
        extension_slice.copy_from_slice(bytes);
        self.size += bytes.len();
        Ok(())
    }

    /// Sets the extension entry at the given index.
    pub fn set_extension_entry(
        &mut self,
        index: usize,
        identifier: u32,
        offset: u32,
    ) -> Result<()> {
        let manifest = self.borrow_manifest_mut()?;
        *manifest
            .extensions
            .entries
            .get_mut(index)
            .ok_or(ImageError::BadExtensionTableIndex)? =
            ManifestExtTableEntry { identifier, offset };
        Ok(())
    }

    /// Adds an extension to the signed region of this `Image`.
    pub fn add_signed_manifest_extensions(&mut self, spec: ManifestExtSpec) -> Result<()> {
        self.add_manifest_extensions(&spec.signed_region, spec.source_path())
    }

    /// Adds an extension to the unsigned region of this `Image`.
    pub fn add_unsigned_manifest_extensions(&mut self, spec: ManifestExtSpec) -> Result<()> {
        self.add_manifest_extensions(&spec.unsigned_region, spec.source_path())
    }

    fn add_manifest_extensions(
        &mut self,
        entries: &[ManifestExtEntrySpec],
        relative_path: Option<&Path>,
    ) -> Result<()> {
        let manifest = self.borrow_manifest()?;

        // A copy of the extension table since we can't borrow as mutable.
        let mut ext_table = manifest.extensions.entries;

        for spec in entries {
            let entry = ManifestExtEntry::from_spec(spec, relative_path)?;
            let entry_id = entry.header().identifier;

            // Update the offset in the extension table.
            let ext_table_entry = ext_table
                .iter_mut()
                .find(|e| e.identifier == entry_id)
                .ok_or(ImageError::NoExtensionTableEntry(entry_id))?;

            // If the extension already exists, overwrite it, else append it to the end of the
            // image.
            let offset = if ext_table_entry.offset != 0 {
                ext_table_entry.offset as usize
            } else {
                ensure!(
                    self.size % align_of::<u32>() == 0,
                    ImageError::BadExtensionAlignment(entry_id)
                );
                self.size
            };
            ext_table_entry.offset = offset as u32;

            // Write the extension to the end of the image.
            let ext_bytes = entry.to_vec();
            let end_index = offset
                .checked_add(ext_bytes.len())
                .ok_or(ImageError::ExtensionOverflow)?;
            let extension_slice = self
                .data
                .bytes
                .get_mut(offset..end_index)
                .ok_or(ImageError::ExtensionOverflow)?;
            extension_slice.copy_from_slice(ext_bytes.as_slice());
            self.size = std::cmp::max(end_index, self.size);
        }

        let mut manifest = self.borrow_manifest_mut()?;
        manifest.extensions.entries = ext_table;

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

    /// Updates the length field in the `Manifest`.
    pub fn update_length(&mut self) -> Result<usize> {
        self.borrow_manifest_mut()?.length = self.size as u32;
        Ok(self.size)
    }

    /// Sets the `signed_reion_end` field to `self.size`.
    /// Note that this method must be called AFTER all signed extensions are added but BEFORE
    /// adding any unsigned extensions.
    pub fn update_signed_region_end(&mut self) -> Result<usize> {
        self.borrow_manifest_mut()?.signed_region_end = self.size as u32;
        Ok(self.size)
    }

    /// Operates on the signed region of the image.
    pub fn map_signed_region<F, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce(&[u8]) -> R,
    {
        Ok(f(&self.data.bytes[offset_of!(Manifest, usage_constraints)
            ..self.borrow_manifest()?.signed_region_end as usize]))
    }

    /// Compute the SHA256 digest for the signed portion of the `Image`.
    pub fn compute_digest(&self) -> Result<sha256::Sha256Digest> {
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
