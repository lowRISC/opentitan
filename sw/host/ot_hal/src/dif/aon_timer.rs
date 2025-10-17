// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum AonTimerReg {
    AlertTest = ot_bindgen_dif::AON_TIMER_ALERT_TEST_REG_OFFSET,
    WkupCtrl = ot_bindgen_dif::AON_TIMER_WKUP_CTRL_REG_OFFSET,
    WkupTholdLo = ot_bindgen_dif::AON_TIMER_WKUP_THOLD_LO_REG_OFFSET,
    WkupTholdHi = ot_bindgen_dif::AON_TIMER_WKUP_THOLD_HI_REG_OFFSET,
    WkupCountLo = ot_bindgen_dif::AON_TIMER_WKUP_COUNT_LO_REG_OFFSET,
    WkupCountHi = ot_bindgen_dif::AON_TIMER_WKUP_COUNT_HI_REG_OFFSET,
    WdogRegwen = ot_bindgen_dif::AON_TIMER_WDOG_REGWEN_REG_OFFSET,
    WdogCtrl = ot_bindgen_dif::AON_TIMER_WDOG_CTRL_REG_OFFSET,
    WdogBarkThold = ot_bindgen_dif::AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET,
    WdogBiteThold = ot_bindgen_dif::AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
    WdogCount = ot_bindgen_dif::AON_TIMER_WDOG_COUNT_REG_OFFSET,
    IntrState = ot_bindgen_dif::AON_TIMER_INTR_STATE_REG_OFFSET,
    IntrTest = ot_bindgen_dif::AON_TIMER_INTR_TEST_REG_OFFSET,
    WkupCause = ot_bindgen_dif::AON_TIMER_WKUP_CAUSE_REG_OFFSET,
}
