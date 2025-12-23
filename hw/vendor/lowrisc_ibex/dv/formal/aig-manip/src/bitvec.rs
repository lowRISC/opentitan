// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/// A memory efficient bit vector, where the bits are packed.
#[derive(Clone, Debug)]
pub struct BitVec {
    len: usize,
    inner: Vec<u64>,
}

impl BitVec {
    pub fn new() -> BitVec {
        BitVec {
            len: 0,
            inner: Vec::new(),
        }
    }

    pub fn fill_zero(len: usize) -> BitVec {
        BitVec {
            len,
            inner: vec![0; len.div_ceil(64)],
        }
    }

    pub fn set(&mut self, idx: usize, value: bool) {
        assert!(idx < self.len);
        if value {
            self.inner[idx / 64] |= 1 << (idx % 64);
        } else {
            self.inner[idx / 64] &= !(1 << (idx % 64));
        }
    }

    pub fn push(&mut self, value: bool) {
        if self.len % 64 == 0 {
            self.inner.push(value as u64);
        } else {
            *self.inner.last_mut().unwrap() |= (value as u64) << (self.len % 64);
        }
        self.len += 1;
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len {
            None
        } else {
            Some((self.inner[index / 64] >> (index % 64)) & 1 != 0)
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = bool> {
        (0..self.len).map(|x| self.get(x).unwrap())
    }
}

impl FromIterator<bool> for BitVec {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut vec = BitVec::new();
        for item in iter {
            vec.push(item);
        }
        vec
    }
}
