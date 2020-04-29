// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![crate_name = "tock"]
#![crate_type = "rlib"]

pub extern crate components;
pub extern crate rv32i;
pub extern crate capsules;
pub extern crate kernel;
pub extern crate tock_rt0;
