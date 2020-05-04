//! Drivers and chip support for the Earlgrey soft core.

#![feature(asm, concat_idents, const_fn, naked_functions)]
#![feature(in_band_lifetimes)]
#![no_std]
#![crate_name = "earlgrey"]
#![crate_type = "rlib"]

mod chip_config;
mod interrupts;

pub mod chip;
pub mod gpio;
pub mod plic;
pub mod timer;
pub mod uart;
