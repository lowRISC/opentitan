// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/// Represents a single field of bits within a u32 word.
pub struct BitField {
    /// Number of bits into the word that the field starts.
    pub offset: u32,
    /// Length in bits of the field.
    pub size: u32,
}

impl BitField {
    /// Create a new BitField with the given offset and length.
    pub const fn new(offset: u32, size: u32) -> BitField {
        BitField { offset, size }
    }

    /// Extract a value of this field from a word.
    pub const fn extract(&self, word: u32) -> u32 {
        (word & self.mask()) >> self.offset
    }

    /// Emplace a value into this field within a word.
    pub const fn emplace(&self, value: u32) -> u32 {
        (value << self.offset) & self.mask()
    }

    /// Returns the bit-mask of this bitfield.
    pub const fn mask(&self) -> u32 {
        let mask = (1 << self.size) - 1;
        mask << self.offset
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic() {
        let bitfield = BitField { offset: 2, size: 3 };

        assert_eq!(bitfield.mask(), 0b0011100);
        assert_eq!(bitfield.extract(0b1110111), 0b101);
        assert_eq!(bitfield.emplace(0b101), 0b0010100);
    }
}
