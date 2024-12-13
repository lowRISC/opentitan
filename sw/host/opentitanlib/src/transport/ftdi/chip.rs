// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub trait Chip {
    const VENDOR_ID: u16 = 0x0403;
    const PRODUCT_ID: u16;

    const UART_BAUD: u32 = 115200;

    const INTERFACES: &'static [ftdi::Interface];
}

pub struct Ft4232hq {}

impl Chip for Ft4232hq {
    const PRODUCT_ID: u16 = 0x6011;
    const INTERFACES: &'static [ftdi::Interface] = &[
        ftdi::Interface::A,
        ftdi::Interface::B,
        // ftdi::Interface::C,
        ftdi::Interface::D,
    ];
}
