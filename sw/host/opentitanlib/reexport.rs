// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Use `extern crate` to force linking of these libraries, so `inventory` registration inside is collected.
extern crate ot_transport_chipwhisperer;
extern crate ot_transport_dediprog;
extern crate ot_transport_ftdi;
extern crate ot_transport_hyperdebug;
extern crate ot_transport_proxy;
extern crate ot_transport_ti50emulator;
extern crate ot_transport_verilator;
extern crate ot_transport_qemu;

pub use opentitanlib_base::*;
