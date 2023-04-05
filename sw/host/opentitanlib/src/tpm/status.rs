// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

pub struct TpmStatus(u32);

impl TpmStatus {
    pub const TPM_GO: u32 = 1 << 5;
    pub const CMD_READY: u32 = 1 << 6;

    pub fn is_valid(&self) -> bool {
        (self.0 >> 7) & 1 == 1
    }

    pub fn data_available(&self) -> bool {
        (self.0 >> 4) & 1 == 1
    }

    pub fn burst_count(&self) -> usize {
        ((self.0 >> 8) & 0xFFFF) as usize
    }

    pub fn _expect(&self) -> bool {
        (self.0 >> 3) & 1 == 1
    }

    pub fn raw_value(&self) -> u32 {
        self.0
    }

    pub fn is_ready(&self) -> bool {
        (self.0 >> 6) & 1 == 1
    }

    pub fn from_bytes(val: [u8; 4]) -> Self {
        Self(u32::from_le_bytes(val))
    }
}

impl fmt::Display for TpmStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Valid: {} Burst: {} Avail: {}",
            self.is_valid(),
            self.burst_count(),
            self.data_available()
        )
    }
}
