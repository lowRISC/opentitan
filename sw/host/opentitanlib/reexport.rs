// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Use `extern crate` to force linking of these libraries, so `inventory` registration inside is collected.
#[cfg(feature = "chipwhisperer")]
extern crate ot_transport_chipwhisperer;
#[cfg(feature = "dediprog")]
extern crate ot_transport_dediprog;
#[cfg(feature = "ftdi")]
extern crate ot_transport_ftdi;
#[cfg(feature = "hyperdebug")]
extern crate ot_transport_hyperdebug;
#[cfg(feature = "proxy")]
extern crate ot_transport_proxy;
#[cfg(feature = "ti50emulator")]
extern crate ot_transport_ti50emulator;
#[cfg(feature = "verilator")]
extern crate ot_transport_verilator;

pub use opentitanlib_base::*;
