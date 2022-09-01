// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

with_unknown! {
    /// From `//sw/device/lib/base/hardened.h`.
    pub enum HardenedBool: u32 {
        True= bindgen::hardened::hardened_bool_kHardenedBoolTrue as u32,
        False= bindgen::hardened::hardened_bool_kHardenedBoolFalse as u32,
    }

    /// From `//sw/device/lib/base/hardened.h`.
    pub enum HardenedByteBool: u8 {
        True= bindgen::hardened::hardened_byte_bool_kHardenedByteBoolTrue as u8,
        False= bindgen::hardened::hardened_byte_bool_kHardenedByteBoolFalse as u8,
    }

    /// From `//sw/device/lib/base/multibits.h`.
    pub enum MultiBitBool4: u8 {
        True= bindgen::multibits::multi_bit_bool_kMultiBitBool4True as u8,
        False= bindgen::multibits::multi_bit_bool_kMultiBitBool4False as u8,
    }

    /// From `//sw/device/lib/base/multibits.h`.
    pub enum MultiBitBool8: u8 {
        True= bindgen::multibits::multi_bit_bool_kMultiBitBool8True as u8,
        False= bindgen::multibits::multi_bit_bool_kMultiBitBool8False as u8,
    }

    /// From `//sw/device/lib/base/multibits.h`.
    pub enum MultiBitBool12: u16 {
        True= bindgen::multibits::multi_bit_bool_kMultiBitBool12True as u16,
        False= bindgen::multibits::multi_bit_bool_kMultiBitBool12False as u16,
    }

    /// From `//sw/device/lib/base/multibits.h`.
    pub enum MultiBitBool16: u16 {
        True= bindgen::multibits::multi_bit_bool_kMultiBitBool16True as u16,
        False= bindgen::multibits::multi_bit_bool_kMultiBitBool16False as u16,
    }
}
