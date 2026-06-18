// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module contains code for working with Verilog `VMEM` files.
//!
//! This includes the [`Vmem'] representation which can be parsed from a string.

use std::iter;

use thiserror::Error;

mod parser;

use parser::VmemParser;
pub use parser::{ParseError, ParseResult};

/// Representation of a VMEM file.
///
/// These files consist of sections which are runs of memory starting at some address.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Vmem {
    sections: Vec<Section>,
}

/// Section of memory at some address in the vmem file.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Section {
    pub addr: u32,
    pub data: Vec<Word>,
}

/// A singular word in a VMEM file, with bytes stored in Big Endian (MSB-first).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Word {
    pub bytes: Vec<u8>,
}

impl Word {
    pub fn new(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }
}

impl Vmem {
    pub fn new(sections: Vec<Section>) -> Self {
        Self { sections }
    }

    /// Parse a complete VMEM file from the contents of a given string.
    pub fn from_str(s: &str, addr_stride: Option<usize>) -> Result<Self, ParseError> {
        VmemParser::parse(s, addr_stride)
    }
}

impl Vmem {
    /// Returns an iterator over sections of the VMEM file.
    pub fn sections(&self) -> impl Iterator<Item = &Section> {
        // Filter out empty sections.
        self.sections
            .iter()
            .filter(|section| !section.data.is_empty())
    }
}

/// Represents some value at some address as specified in the VMEM file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Data {
    pub addr: u32,
    pub value: Word,
}

impl Vmem {
    /// Returns an iterator over all data of the VMEM file.
    ///
    /// The stride should either be 1 (one address per word) or the number of bytes
    /// in each word.
    pub fn data_addrs(&self, stride: usize) -> impl Iterator<Item = Data> + '_ {
        self.sections()
            .flat_map(move |section| section.data_addrs(stride))
    }

    /// Merge any contiguous sections in the VMEM together.
    pub fn merge_sections(&mut self, addr_stride: Option<usize>) {
        self.sections.dedup_by(|sec, last| {
            let nwords = last.data.len() as u32;
            let size = nwords * addr_stride.unwrap_or(1) as u32;
            let merge: bool = last.addr + size == sec.addr;
            if merge {
                last.data.append(&mut sec.data);
            }
            merge
        })
    }
}

impl Section {
    /// Returns an iterator over all data of this section of the VMEM file.
    ///
    /// The stride should either be 1 (one address per word) or the number of bytes
    /// in each word.
    pub fn data_addrs(&self, stride: usize) -> impl Iterator<Item = Data> + '_ {
        let addrs = (self.addr..).step_by(stride);
        let values = self.data.iter();
        iter::zip(addrs, values).map(|(addr, value)| Data {
            addr,
            value: value.clone(),
        })
    }
}

/// Errors that occur when converting VMEM sections
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ConversionError {
    /// Cannot fit the words into the integer format being converted to.
    #[error("word size {0} too large to fit after conversion")]
    InvalidWordSize(usize),
}

impl TryFrom<Section> for Vec<u32> {
    type Error = ConversionError;

    fn try_from(section: Section) -> Result<Self, Self::Error> {
        section
            .data
            .into_iter()
            .map(|mut word| {
                if word.bytes.len() <= 4 {
                    return Err(ConversionError::InvalidWordSize(word.bytes.len()));
                }

                word.bytes.resize(4, 0);
                let bytes: [u8; 4] = word.bytes.try_into().unwrap();
                Ok(u32::from_le_bytes(bytes))
            })
            .collect()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn vmem_data() {
        let vmem = Vmem::from_str("@10 12 23 34 @20 @26 45", Some(4)).unwrap();
        let expected =
            [(0x40, 0x12), (0x44, 0x23), (0x48, 0x34), (0x98, 0x45)].map(|(addr, value)| Data {
                addr,
                value: Word::new(vec![value]),
            });

        let data: Vec<_> = vmem.data_addrs(4).collect();
        assert_eq!(data, expected);
    }

    #[test]
    fn merge_contiguous_sections() {
        // Use a VMEM with word address stride, but convert to byte addresses when parsing & merging.
        let mut vmem = Vmem::from_str("1234 @20 0123 4567 89ab @23 cdef 1f1f", Some(2)).unwrap();
        let expected = vec![
            Section {
                addr: 0x0,
                data: vec![Word::new(vec![0x12, 0x34])],
            },
            Section {
                addr: 0x40,
                data: [
                    [0x01, 0x23],
                    [0x45, 0x67],
                    [0x89, 0xab],
                    [0xcd, 0xef],
                    [0x1f, 0x1f],
                ]
                .iter()
                .map(|&bytes| Word::new(Vec::from(bytes)))
                .collect(),
            },
        ];

        vmem.merge_sections(Some(2));
        assert_eq!(vmem.sections, expected);

        // Use a VMEM with byte address stride directly - no bytes per word is given when parsing.
        let mut vmem = Vmem::from_str("1234 @20 0123 4567 89ab @26 cdef 1f1f", None).unwrap();
        let expected = vec![
            Section {
                addr: 0x0,
                data: vec![Word::new(vec![0x12, 0x34])],
            },
            Section {
                addr: 0x20,
                data: [
                    [0x01, 0x23],
                    [0x45, 0x67],
                    [0x89, 0xab],
                    [0xcd, 0xef],
                    [0x1f, 0x1f],
                ]
                .iter()
                .map(|&bytes| Word::new(Vec::from(bytes)))
                .collect(),
            },
        ];

        vmem.merge_sections(Some(2));
        assert_eq!(vmem.sections, expected);
    }

    #[test]
    fn section_data() {
        let section = Section {
            addr: 0x42,
            data: [0x12, 0x23, 0x34, 0x45]
                .iter()
                .map(|&b| Word::new(vec![b]))
                .collect(),
        };
        let expected =
            [(0x42, 0x12), (0x46, 0x23), (0x4a, 0x34), (0x4e, 0x45)].map(|(addr, value)| Data {
                addr,
                value: Word::new(vec![value]),
            });

        let data: Vec<_> = section.data_addrs(4).collect();
        assert_eq!(data, expected);
    }

    #[test]
    fn section_stride() {
        let section = Section {
            addr: 0x15,
            data: [0x12, 0x45, 0x78, 0xab]
                .iter()
                .map(|&b| Word::new(vec![b]))
                .collect(),
        };

        let expected =
            [(0x15, 0x12), (0x16, 0x45), (0x17, 0x78), (0x18, 0xab)].map(|(addr, value)| Data {
                addr,
                value: Word::new(vec![value]),
            });
        let data: Vec<_> = section.data_addrs(1).collect();
        assert_eq!(data, expected);

        let expected =
            [(0x15, 0x12), (0x1a, 0x45), (0x1f, 0x78), (0x24, 0xab)].map(|(addr, value)| Data {
                addr,
                value: Word::new(vec![value]),
            });
        let data: Vec<_> = section.data_addrs(5).collect();
        assert_eq!(data, expected);
    }
}
