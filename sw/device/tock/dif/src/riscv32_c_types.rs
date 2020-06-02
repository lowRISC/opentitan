// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#[allow(nonstandard_style)]
pub type c_int = i32;
#[allow(nonstandard_style)]
pub type c_uint = u32;
#[allow(nonstandard_style)]
pub type c_longlong = i64;
#[allow(nonstandard_style)]
pub type c_ulonglong = u64;

pub use core::ffi::c_void;
