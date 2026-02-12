// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

with_unknown! {
    /// From `//sw/device/lib/base/hardened.h`.
    pub enum HardenedBool: u32 [default = Self::False] {
        True = bindgen::hardened::hardened_bool_kHardenedBoolTrue,
        False = bindgen::hardened::hardened_bool_kHardenedBoolFalse,
    }

    /// From `//sw/device/lib/base/hardened.h`.
    pub enum HardenedByteBool: u8 [default = Self::False] {
        True = bindgen::hardened::hardened_byte_bool_kHardenedByteBoolTrue as u8,
        False = bindgen::hardened::hardened_byte_bool_kHardenedByteBoolFalse as u8,
    }
}
