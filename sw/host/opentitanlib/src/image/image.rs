// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use memoffset::offset_of;
use std::collections::HashSet;
use std::convert::TryInto;
use std::fs::File;
use std::io::{Read, Write};
use std::mem::{align_of, size_of};
use std::path::{Path, PathBuf};
use thiserror::Error;

use crate::crypto::rsa::Modulus;
use crate::crypto::rsa::Signature as RsaSignature;
use crate::crypto::sha256;
use crate::image::manifest::Manifest;
use crate::image::manifest_def::{ManifestRsaBuffer, ManifestSpec};
use crate::image::manifest_ext::{ManifestExtEntry, ManifestExtSpec};
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
    #[error("Invalid placement of signed extension 0x{0:x}.")]
    MisplacedSignedExtension(u32),
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

    /// Perform a sanity check to ensure that the image comes with manifest.
    ///
    /// Note that passing the sanity check doesn't guarantee that the manifest is valid.
    pub fn manifest_sanity_check(&self) -> Result<()> {
        let manifest = self.borrow_manifest()?;
        let len = self.data.bytes.len() as u32;

        ensure!(manifest.signed_region_end < len);
        ensure!(manifest.length < len);
        ensure!(manifest.code_start < len);
        ensure!(manifest.code_end < len);
        ensure!(manifest.entry_point < len);
        ensure!(manifest.extensions.entries.iter().all(|x| x.offset < len));

        Ok(())
    }

    /// Overwrites all fields in the image's manifest that are defined in `other`.
    pub fn overwrite_manifest(&mut self, other: ManifestSpec) -> Result<()> {
        let manifest = self.borrow_manifest_mut()?;
        let mut manifest_def: ManifestSpec = (&*manifest).try_into()?;
        manifest_def.overwrite_fields(other);
        *manifest = manifest_def.try_into()?;
        Ok(())
    }

    /// Adds an extension to the signed region of this `Image`.
    ///
    /// This will take all the extensions in `spec.signed_region` and append them to the image.
    /// This should be called before adding any unsigned extensions to ensure all extensions that
    /// are a part of the signature exist within the contiguous signed region of the image.
    pub fn add_signed_manifest_extensions(&mut self, spec: &ManifestExtSpec) -> Result<()> {
        for entry_spec in &spec.signed_region {
            self.add_manifest_extension(ManifestExtEntry::from_spec(
                entry_spec,
                spec.source_path(),
            )?)?;
        }
        Ok(())
    }

    /// Adds an extension to the unsigned region of this `Image`.
    ///
    /// This will take all the extensions in `spec.unsigned_region` and append them to the image.
    /// This should only be called once all signed extensions have been added.
    pub fn add_unsigned_manifest_extensions(&mut self, spec: &ManifestExtSpec) -> Result<()> {
        for entry_spec in &spec.unsigned_region {
            self.add_manifest_extension(ManifestExtEntry::from_spec(
                entry_spec,
                spec.source_path(),
            )?)?;
        }
        Ok(())
    }

    /// Adds an extension to the end of this `Image`.
    pub fn add_manifest_extension(&mut self, entry: ManifestExtEntry) -> Result<()> {
        let manifest = self.borrow_manifest()?;

        // A copy of the extension table since we can't borrow as mutable.
        let mut ext_table = manifest.extensions.entries;

        let entry_id = entry.header().identifier;

        // Update the offset in the extension table.
        let ext_table_entry = ext_table
            .iter_mut()
            .find(|e| e.identifier == entry_id)
            .ok_or(ImageError::NoExtensionTableEntry(entry_id))?;

        // If the extension already exists, overwrite it, else append it to the end of the
        // image.
        let offset = if ext_table_entry.offset != 0 {
            ext_table_entry.offset
        } else {
            ensure!(
                self.size % align_of::<u32>() == 0,
                ImageError::BadExtensionAlignment(entry_id)
            );
            self.size.try_into()?
        };
        ext_table_entry.offset = offset;

        // Write the extension to the end of the image.
        let ext_bytes = entry.to_vec();
        let end_index = offset
            .checked_add(ext_bytes.len().try_into()?)
            .ok_or(ImageError::ExtensionOverflow)?;
        let extension_slice = self
            .data
            .bytes
            .get_mut(offset as usize..end_index as usize)
            .ok_or(ImageError::ExtensionOverflow)?;
        extension_slice.copy_from_slice(ext_bytes.as_slice());
        self.size = std::cmp::max(end_index as usize, self.size);

        let manifest = self.borrow_manifest_mut()?;
        manifest.extensions.entries = ext_table;

        Ok(())
    }

    /// Allocates space for a manifest extension and sets the offset in the extension table.
    ///
    /// This function is similar to `add_manifest_extension`, but doesn't populate any data for the
    /// extension. This is necessary to properly set the `length` field of the manifest and the
    /// `offset` field of the manifest extension entry for signing.
    pub fn allocate_manifest_extension(&mut self, id: u32, len: usize) -> Result<()> {
        let offset = self.size as u32;
        self.borrow_manifest_mut()?
            .extensions
            .entries
            .iter_mut()
            .find(|e| e.identifier == id)
            .ok_or(ImageError::NoExtensionTableEntry(id))?
            .offset = offset;

        self.size = self
            .size
            .checked_add(len)
            .ok_or(ImageError::ExtensionOverflow)?;

        Ok(())
    }

    /// Clears any entry in the manifest extension table that doesn't have an offset.
    ///
    /// This allows a manifest definition with a populated extension table to be used even when
    /// extensions aren't provided.
    pub fn drop_null_extensions(&mut self) -> Result<()> {
        let manifest = self.borrow_manifest()?;

        manifest.extensions.entries.map(|mut e| {
            if e.offset == 0 {
                e.identifier = 0;
            }
        });

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
        let manifest_layout: zerocopy::Ref<_, Manifest> =
            zerocopy::Ref::new(manifest_slice).ok_or(ImageError::Parse)?;
        let manifest: &Manifest = manifest_layout.into_ref();
        Ok(manifest)
    }

    pub fn borrow_manifest_mut(&mut self) -> Result<&mut Manifest> {
        let manifest_slice = &mut self.data.bytes[0..size_of::<Manifest>()];
        let manifest_layout: zerocopy::Ref<_, Manifest> =
            zerocopy::Ref::new(manifest_slice).ok_or(ImageError::Parse)?;
        let manifest: &mut Manifest = manifest_layout.into_mut();
        Ok(manifest)
    }

    /// Updates the length field in the `Manifest`.
    pub fn update_length(&mut self) -> Result<usize> {
        self.borrow_manifest_mut()?.length = self.size as u32;
        Ok(self.size)
    }

    /// Sets the `signed_region_end` field to the end of the last signed extension.
    ///
    /// The end of the signed region is computed as the offset of the first extension that is not
    /// in `signed_ids` or the size of the image if there is no such extension.
    pub fn update_signed_region(&mut self, signed_ids: &HashSet<u32>) -> Result<()> {
        let image_size = self.size as u32;
        let mut first_unsigned_ext = 0u32;
        let manifest = self.borrow_manifest_mut()?;

        let mut ext_table = manifest.extensions.entries;
        ext_table.sort_by(|a, b| a.offset.cmp(&b.offset));
        for e in ext_table {
            // Ignore any extensions that haven't been added to the image.
            if e.offset == 0 {
                continue;
            }
            if signed_ids.contains(&e.identifier) {
                // Since extensions are sorted by offset, if we've already seen an unsigned
                // extension then the signed region is discontinuous.
                ensure!(
                    first_unsigned_ext == 0,
                    ImageError::MisplacedSignedExtension(e.identifier)
                );
            } else if first_unsigned_ext == 0 {
                first_unsigned_ext = e.offset;
            }
        }

        manifest.signed_region_end = if first_unsigned_ext == 0 {
            image_size
        } else {
            first_unsigned_ext
        };

        Ok(())
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
