// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module contains code for working with Verilog `vmem` files.
//!
//! This includes the [`Vmem'] representation which can be parsed from a string.

use std::iter;
use std::str::FromStr;

mod parser;

use parser::VmemParser;
pub use parser::{ParseError, ParseResult};

/// Representation of a vmem file.
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
    pub data: Vec<u32>,
}

impl FromStr for Vmem {
    type Err = ParseError;

    /// Parse the vmem file from a complete string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        VmemParser::parse(s)
    }
}

impl Vmem {
    /// Returns an iterator over sections of the vmem file.
    pub fn sections(&self) -> impl Iterator<Item = &Section> {
        // Filter out empty sections.
        self.sections
            .iter()
            .filter(|section| !section.data.is_empty())
    }
}

/// Represents some value at some address as specified in the vmem file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Data {
    pub addr: u32,
    pub value: u32,
}

impl Vmem {
    /// Returns an iterator over all data of the vmem file.
    pub fn data_addrs(&self) -> impl Iterator<Item = Data> + '_ {
        self.sections().flat_map(|section| section.data_addrs())
    }

    /// Merge all continguous sections together in one section
    pub fn merge_sections(&mut self) {
        let mut res: Vec<Section> = Vec::new();
        // we modify in place as much as possible to avoid copying data uselessly
        for mut sec in std::mem::take(&mut self.sections) {
            match res.last_mut() {
                Some(ref mut last) if { last.addr + last.data.len() as u32 * 4 == sec.addr } => {
                    last.data.append(&mut sec.data)
                }
                _ => res.push(sec),
            }
        }
        self.sections = res
    }
}

impl Section {
    /// Returns an iterator over all data of this section of the vmem file.
    pub fn data_addrs(&self) -> impl Iterator<Item = Data> + '_ {
        let addrs = (self.addr..).step_by(4);
        let values = self.data.iter();
        iter::zip(addrs, values).map(|(addr, value)| Data {
            addr,
            value: *value,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn vmem_data() {
        let vmem = Vmem::from_str("@10 12 23 34 @20 @26 45").unwrap();
        let expected = [(0x40, 0x12), (0x44, 0x23), (0x48, 0x34), (0x98, 0x45)]
            .map(|(addr, value)| Data { addr, value });

        let data: Vec<_> = vmem.data_addrs().collect();
        assert_eq!(data, expected);
    }

    #[test]
    fn section_data() {
        let section = Section {
            addr: 0x42,
            data: vec![0x12, 0x23, 0x34, 0x45],
        };
        let expected = [(0x42, 0x12), (0x46, 0x23), (0x4a, 0x34), (0x4e, 0x45)]
            .map(|(addr, value)| Data { addr, value });

        let data: Vec<_> = section.data_addrs().collect();
        assert_eq!(data, expected);
    }
}
