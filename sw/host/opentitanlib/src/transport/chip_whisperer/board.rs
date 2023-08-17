// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub trait Board {
    const VENDOR_ID: u16 = 0x2b3e;
    const PRODUCT_ID: u16;

    // Pins needed for SPI on the Chip Whisperer board.
    const PIN_CLK: &'static str;
    const PIN_SDI: &'static str;
    const PIN_SDO: &'static str;
    const PIN_CS: &'static str;
    // Pins needed for reset & bootstrap on the Chip Whisperer board.
    const PIN_TRST: &'static str;
    const PIN_POR_N: &'static str;
    const PIN_SW_STRAP0: &'static str;
    const PIN_SW_STRAP1: &'static str;
    const PIN_SW_STRAP2: &'static str;
    const PIN_TAP_STRAP0: &'static str;
    const PIN_TAP_STRAP1: &'static str;
}

pub struct Cw310 {}

impl Board for Cw310 {
    const PRODUCT_ID: u16 = 0xc310;

    // Pins needed for SPI on the Chip Whisperer board.
    const PIN_CLK: &'static str = "USB_SPI_SCK";
    const PIN_SDI: &'static str = "USB_SPI_COPI";
    const PIN_SDO: &'static str = "USB_SPI_CIPO";
    const PIN_CS: &'static str = "USB_SPI_CS";
    // Pins needed for reset & bootstrap on the Chip Whisperer board.
    const PIN_TRST: &'static str = "USB_A13";
    const PIN_POR_N: &'static str = "USB_A14";
    const PIN_SW_STRAP0: &'static str = "USB_A15";
    const PIN_SW_STRAP1: &'static str = "USB_A16";
    const PIN_SW_STRAP2: &'static str = "USB_A17";
    const PIN_TAP_STRAP0: &'static str = "USB_A18";
    const PIN_TAP_STRAP1: &'static str = "USB_A19";
}
