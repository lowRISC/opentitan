// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use bindgen::dif;
use bitflags::bitflags;

bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct PinmuxPadAttr: u32 {
        const OD_EN = 0b1 << dif::PINMUX_MIO_PAD_ATTR_1_OD_EN_1_BIT;
        const SCHMITT_EN = 0b1 << dif::PINMUX_MIO_PAD_ATTR_1_SCHMITT_EN_1_BIT;
        const KEEPER_EN = 0b1 << dif::PINMUX_MIO_PAD_ATTR_1_KEEPER_EN_1_BIT;
        const PULL_SELECT = 0b1 << dif::PINMUX_MIO_PAD_ATTR_1_PULL_SELECT_1_BIT;
        const PULL_EN = 0b1 << dif::PINMUX_MIO_PAD_ATTR_1_PULL_EN_1_BIT;
        const VIRTUAL_OD_EN = 0b1 << dif::PINMUX_MIO_PAD_ATTR_1_VIRTUAL_OD_EN_1_BIT;
        const INVERT = 0b1 << dif::PINMUX_MIO_PAD_ATTR_1_INVERT_1_BIT;
    }
}
