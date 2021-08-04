// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub struct BitField {
    pub offset: u32,
    pub size: u32,
}

impl BitField {
    pub fn new(offset: u32, size: u32) -> BitField {
        BitField { offset, size }
    }

    pub fn extract(&self, word: u32) -> u32 {
        let mask = (1 << self.size) - 1;
        (word >> self.offset) & mask
    }
}
