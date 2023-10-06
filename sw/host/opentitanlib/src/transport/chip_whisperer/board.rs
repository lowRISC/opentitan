// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub trait Board {
    const VENDOR_ID: u16 = 0x2b3e;
    const PRODUCT_ID: u16;

    // Pins needed for reset & bootstrap on the Chip Whisperer board.
    const PIN_POR_N: &'static str;
}

pub struct Cw310 {}

impl Board for Cw310 {
    const PRODUCT_ID: u16 = 0xc310;

    // Pins needed for reset & bootstrap on the Chip Whisperer board.
    const PIN_POR_N: &'static str = "USB_A14";
}

pub struct Cw340 {}

impl Board for Cw340 {
    const PRODUCT_ID: u16 = 0xc340;

    // Pins needed for reset & bootstrap on the Chip Whisperer board.
    const PIN_POR_N: &'static str = "PC30";
}
