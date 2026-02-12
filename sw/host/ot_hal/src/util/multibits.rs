// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

with_unknown! {
    /// From `//sw/device/lib/base/multibits.h`.
    pub enum MultiBitBool4: u8 [default = Self::False] {
        True = ot_bindgen_multibits::multi_bit_bool_kMultiBitBool4True as u8,
        False = ot_bindgen_multibits::multi_bit_bool_kMultiBitBool4False as u8,
    }

    /// From `//sw/device/lib/base/multibits.h`.
    pub enum MultiBitBool8: u8 [default = Self::False] {
        True = ot_bindgen_multibits::multi_bit_bool_kMultiBitBool8True as u8,
        False = ot_bindgen_multibits::multi_bit_bool_kMultiBitBool8False as u8,
    }

    /// From `//sw/device/lib/base/multibits.h`.
    pub enum MultiBitBool12: u16 [default = Self::False] {
        True = ot_bindgen_multibits::multi_bit_bool_kMultiBitBool12True as u16,
        False = ot_bindgen_multibits::multi_bit_bool_kMultiBitBool12False as u16,
    }

    /// From `//sw/device/lib/base/multibits.h`.
    pub enum MultiBitBool16: u16 [default = Self::False] {
        True = ot_bindgen_multibits::multi_bit_bool_kMultiBitBool16True as u16,
        False = ot_bindgen_multibits::multi_bit_bool_kMultiBitBool16False as u16,
    }
}
