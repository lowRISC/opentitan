// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings)]
#![deny(unused)]
#![deny(unsafe_code)]

use crate::manifest;
use thiserror::Error;

#[derive(Error, Debug, PartialEq)]
pub enum ImageError {
    #[error("Expected at most {len} bytes for offset {offset}, received {data_len}.")]
    FieldData {
        offset: usize,
        len: usize,
        data_len: usize,
    },
}

/// A thin wrapper around a Vec to help with setting ROM_EXT manifest fields.
#[derive(Debug)]
pub struct Image {
    data: Vec<u8>,
}

impl Image {
    /// Sets the value of a ROM_EXT manifest field.
    pub fn set_manifest_field<I>(
        &mut self,
        field: &manifest::ManifestField,
        field_data: I,
    ) -> Result<(), ImageError>
    where
        I: IntoIterator<Item = u8>,
        I::IntoIter: ExactSizeIterator,
    {
        let field_data = field_data.into_iter();
        if field_data.len() > field.size_bytes {
            Err(ImageError::FieldData {
                offset: field.offset,
                len: field.size_bytes,
                data_len: field_data.len(),
            })
        } else {
            self.data.splice(
                field.offset..(field.offset + field_data.len()),
                field_data,
            );
            Ok(())
        }
    }

    /// Returns the signed bytes of the image.
    pub fn signed_bytes(&self) -> &[u8] {
        &self.data[manifest::ROM_EXT_SIGNED_AREA_START_OFFSET..]
    }
}

impl AsRef<[u8]> for Image {
    fn as_ref(&self) -> &[u8] {
        &self.data
    }
}

impl From<Vec<u8>> for Image {
    fn from(data: Vec<u8>) -> Self {
        Image { data }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_manifest_field() -> Result<(), ImageError> {
        let mut image = Image::from(vec![0; 1024]);
        let field = manifest::ROM_EXT_IMAGE_LENGTH;
        let val: [u8; 4] = [0xA5; 4];
        image.set_manifest_field(&field, val.iter().cloned())?;
        assert_eq!(
            image.as_ref()[field.offset..field.offset + field.size_bytes],
            val
        );
        Ok(())
    }

    #[test]
    fn test_set_manifest_field_error() {
        let mut image = Image::from(vec![0; 1024]);
        let field = manifest::ROM_EXT_IMAGE_LENGTH;
        let val: [u8; 6] = [0xA5; 6];
        assert_eq!(
            image.set_manifest_field(&field, val.iter().cloned()),
            Err(ImageError::FieldData {
                offset: field.offset,
                len: field.size_bytes,
                data_len: 6
            })
        );
    }

    #[test]
    fn test_signed_bytes() -> Result<(), ImageError> {
        let mut image = Image::from(vec![0; 1024]);
        let field = manifest::ROM_EXT_IMAGE_SIGNATURE;
        let val: [u8; manifest::ROM_EXT_IMAGE_SIGNATURE.size_bytes] =
            [0xA5; manifest::ROM_EXT_IMAGE_SIGNATURE.size_bytes];
        image.set_manifest_field(&field, val.iter().cloned())?;
        assert_eq!(
            image.as_ref()[field.offset..field.offset + field.size_bytes],
            val
        );
        Ok(())
    }
}
