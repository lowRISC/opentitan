// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use bitflags::bitflags;

use bindgen::dif;

use crate::util::bitfield::BitField;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum ClkmgrReg {
    AlertTest = dif::CLKMGR_ALERT_TEST_REG_OFFSET,
    ExtclkCtrlRegwen = dif::CLKMGR_EXTCLK_CTRL_REGWEN_REG_OFFSET,
    ExtclkCtrl = dif::CLKMGR_EXTCLK_CTRL_REG_OFFSET,
    ExtclkStatus = dif::CLKMGR_EXTCLK_STATUS_REG_OFFSET,
    JitterRegwen = dif::CLKMGR_JITTER_REGWEN_REG_OFFSET,
    JitterEnable = dif::CLKMGR_JITTER_ENABLE_REG_OFFSET,
    ClkEnables = dif::CLKMGR_CLK_ENABLES_REG_OFFSET,
    ClkHints = dif::CLKMGR_CLK_HINTS_REG_OFFSET,
    ClkHintsStatus = dif::CLKMGR_CLK_HINTS_STATUS_REG_OFFSET,
    MeasureCtrlRegwen = dif::CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET,
    IoMeasCtrlEn = dif::CLKMGR_IO_MEAS_CTRL_EN_REG_OFFSET,
    IoMeasCtrlShadowed = dif::CLKMGR_IO_MEAS_CTRL_SHADOWED_REG_OFFSET,
    IoDiv2MeasCtrlEn = dif::CLKMGR_IO_DIV2_MEAS_CTRL_EN_REG_OFFSET,
    IoDiv2MeasCtrlShadowed = dif::CLKMGR_IO_DIV2_MEAS_CTRL_SHADOWED_REG_OFFSET,
    IoDiv4MeasCtrlEn = dif::CLKMGR_IO_DIV4_MEAS_CTRL_EN_REG_OFFSET,
    IoDiv4MeasCtrlShadowed = dif::CLKMGR_IO_DIV4_MEAS_CTRL_SHADOWED_REG_OFFSET,
    MainMeasCtrlEn = dif::CLKMGR_MAIN_MEAS_CTRL_EN_REG_OFFSET,
    MainMeasCtrlShadowed = dif::CLKMGR_MAIN_MEAS_CTRL_SHADOWED_REG_OFFSET,
    UsbMeasCtrlEn = dif::CLKMGR_USB_MEAS_CTRL_EN_REG_OFFSET,
    UsbMeasCtrlShadowed = dif::CLKMGR_USB_MEAS_CTRL_SHADOWED_REG_OFFSET,
    RecovErrCode = dif::CLKMGR_RECOV_ERR_CODE_REG_OFFSET,
    FatalErrCode = dif::CLKMGR_FATAL_ERR_CODE_REG_OFFSET,
}

bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct ClkmgrExtclkCtrlRegwen: u32 {
        const EN = 0b1 << dif::CLKMGR_EXTCLK_CTRL_REGWEN_EN_BIT;
    }
}

/// BitFields for the CLKMGR_EXTCLK_CTRL register.
pub struct ClkmgrExtclkCtrl;

impl ClkmgrExtclkCtrl {
    pub const HI_SPEED_SEL: BitField = BitField {
        offset: dif::CLKMGR_EXTCLK_CTRL_HI_SPEED_SEL_OFFSET,
        // Relies on mask being continuous
        size: dif::CLKMGR_EXTCLK_CTRL_HI_SPEED_SEL_MASK.count_ones(),
    };

    pub const SEL: BitField = BitField {
        offset: dif::CLKMGR_EXTCLK_CTRL_SEL_OFFSET,
        // Relies on mask being continuous
        size: dif::CLKMGR_EXTCLK_CTRL_SEL_MASK.count_ones(),
    };
}
