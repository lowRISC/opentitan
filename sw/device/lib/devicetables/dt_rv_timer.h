// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_TIMER_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_TIMER_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtRvTimerRegBlockCore = 0,
  kDtRvTimerRegBlockCount = 1,
} dt_rv_timer_reg_block_t;

typedef enum {
  kDtRvTimerIrqTypeTimerExpiredHart0Timer0 = 0,
  kDtRvTimerIrqTypeCount = 1,
} dt_rv_timer_irq_type_t;

typedef enum {
  kDtRvTimerClockClk = 0,
  kDtRvTimerClockCount = 1,
} dt_rv_timer_clock_t;

typedef enum {
  kDtRvTimerPinctrlInputCount = 0,
  kDtRvTimerPinctrlOutputCount = 0,
} dt_rv_timer_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_TIMER_H_
