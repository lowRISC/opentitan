// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::image::manifest::Manifest;
use crate::image::manifest_def::ManifestDef;
use crate::util::parse_int::ParseInt;
use anyhow::{ensure, Result};
use std::convert::TryInto;
use std::fs::File;
use std::io::{Read, Write};
use std::mem::size_of;
use std::path::{Path, PathBuf};
use thiserror::Error;

use zerocopy::LayoutVerified;

#[derive(Debug, Error)]
pub enum ImageError {
    #[error("Incomplete read: expected to read {0} bytes but read {1} bytes")]
    IncompleteRead(usize, usize),
    #[error("Failed to parse image manifest.")]
    Parse,
}

#[repr(C)]
#[derive(Debug)]
pub struct Image {
    bytes: Vec<u8>,
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

impl Image {
    /// Creates an `Image` from a given input binary.
    pub fn read_from_file(path: &Path) -> Result<Image> {
        let file_len = path.metadata()?.len() as usize;
        // Create a buffer with the same alignment as Manifest that's as least as long as the input
        // file.
        let mut aligned: Vec<Manifest> =
            Vec::with_capacity((0..file_len).step_by(size_of::<Manifest>()).len());

        // Convert the aligned buffer to a Vec<u8> with the same capacity, but length equal to the
        // size of the input file.
        let vec_ptr = aligned.as_mut_ptr() as *mut u8;
        let vec_cap = aligned.capacity() * size_of::<Manifest>();

        // Forget `aligned` so we don't double free.
        std::mem::forget(aligned);

        // Convert our `aligned` Vec<Manifest> to a Vec<u8> with the same capacity and len equal to
        // the size of the input image. This should mean that the new Vec<u8> has the same
        // alignment as Manifest so we can successfully use LayoutVerified later to reinterpret the
        // head of the image as a Manifest.
        let mut buf: Vec<u8> = unsafe { Vec::from_raw_parts(vec_ptr, file_len, vec_cap) };

        // Read the image into our buffer.
        let mut file = File::open(path)?;
        file.read(&mut *buf)?;

        Ok(Image { bytes: buf })
    }

    /// Write out the `Image` to a file at the given `path`.
    pub fn write_to_file(self, path: &Path) -> Result<()> {
        let mut file = File::create(path)?;
        file.write(self.bytes.as_slice())?;
        Ok(())
    }

    /// Overwrites all fields in the image's manifest that are defined in `other`.
    pub fn overwrite_manifest(&mut self, other: ManifestDef) -> Result<()> {
        let (manifest_slice, _) = self.bytes.split_at_mut(size_of::<Manifest>());
        let manifest_layout: LayoutVerified<&mut [u8], Manifest> =
            LayoutVerified::new(&mut *manifest_slice).ok_or(ImageError::Parse)?;
        let manifest: &mut Manifest = manifest_layout.into_mut();
        let mut manifest_def: ManifestDef = (&*manifest).try_into()?;
        manifest_def.overwrite_fields(other);
        *manifest = manifest_def.try_into()?;
        Ok(())
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
        File::open(&testdata!("test_image.bin"))
            .unwrap()
            .read_to_end(&mut orig_bytes)
            .unwrap();
        File::open(&testdata!("test_image_out.bin"))
            .unwrap()
            .read_to_end(&mut res_bytes)
            .unwrap();
        assert_eq!(orig_bytes, res_bytes);
    }
}
