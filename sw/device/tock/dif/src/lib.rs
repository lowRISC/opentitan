// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Bindings for OpenTitan DIF libaries

#![no_std]
#![crate_name = "dif"]
#![crate_type = "rlib"]

#[allow(nonstandard_style)]
pub mod dif_bind {
    include!(concat!(env!("OUT_DIR"), "/ot_dif_bindings.rs"));
}

pub mod riscv32_c_types;
