//! Implementations for generic LowRISC peripherals.

#![feature(asm, concat_idents, const_fn, core_intrinsics)]
#![feature(in_band_lifetimes)]
#![feature(exclusive_range_pattern)]
#![no_std]
#![crate_name = "opentitan_common"]
#![crate_type = "rlib"]

pub mod gpio;
pub mod uart;
