// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub trait Board {
    const VENDOR_ID: u16 = 0x2b3e;
    const PRODUCT_ID: u16;

    const UART_BAUD: u32 = 115200;
}

pub struct Cw310 {}

impl Board for Cw310 {
    const PRODUCT_ID: u16 = 0xc310;
}

pub struct Cw340 {}

impl Board for Cw340 {
    const PRODUCT_ID: u16 = 0xc340;
}
