// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum AonTimerReg {
    AlertTest = bindgen::dif::AON_TIMER_ALERT_TEST_REG_OFFSET,
    WkupCtrl = bindgen::dif::AON_TIMER_WKUP_CTRL_REG_OFFSET,
    WkupTholdLo = bindgen::dif::AON_TIMER_WKUP_THOLD_LO_REG_OFFSET,
    WkupTholdHi = bindgen::dif::AON_TIMER_WKUP_THOLD_HI_REG_OFFSET,
    WkupCountLo = bindgen::dif::AON_TIMER_WKUP_COUNT_LO_REG_OFFSET,
    WkupCountHi = bindgen::dif::AON_TIMER_WKUP_COUNT_HI_REG_OFFSET,
    WdogRegwen = bindgen::dif::AON_TIMER_WDOG_REGWEN_REG_OFFSET,
    WdogCtrl = bindgen::dif::AON_TIMER_WDOG_CTRL_REG_OFFSET,
    WdogBarkThold = bindgen::dif::AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET,
    WdogBiteThold = bindgen::dif::AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
    WdogCount = bindgen::dif::AON_TIMER_WDOG_COUNT_REG_OFFSET,
    IntrState = bindgen::dif::AON_TIMER_INTR_STATE_REG_OFFSET,
    IntrTest = bindgen::dif::AON_TIMER_INTR_TEST_REG_OFFSET,
    WkupCause = bindgen::dif::AON_TIMER_WKUP_CAUSE_REG_OFFSET,
}
