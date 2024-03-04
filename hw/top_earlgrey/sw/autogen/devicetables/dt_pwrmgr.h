// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_PWRMGR_H_
#define OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_PWRMGR_H_

#include "sw/device/lib/devicetables/dt.h"
#include <stdint.h>

typedef enum {
  kDtPwrmgrRegBlockCore = 0,
  kDtPwrmgrRegBlockCount = 1,
} dt_pwrmgr_reg_block_t;

typedef enum {
  kDtPwrmgrIrqTypeWakeup = 0,
  kDtPwrmgrIrqTypeCount = 1,
} dt_pwrmgr_irq_type_t;

typedef enum {
  kDtPwrmgrClockClk = 0,
  kDtPwrmgrClockSlow = 1,
  kDtPwrmgrClockLc = 2,
  kDtPwrmgrClockEsc = 3,
  kDtPwrmgrClockCount = 4,
} dt_pwrmgr_clock_t;

typedef enum {
  kDtPwrmgrPinctrlInputCount = 0,
  kDtPwrmgrPinctrlOutputCount = 0,
} dt_pwrmgr_pinctrl_t;

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_PWRMGR_H_
