// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_AON_TIMER_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_AON_TIMER_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtAonTimerRegBlockCore = 0,
  kDtAonTimerRegBlockCount = 1,
} dt_aon_timer_reg_block_t;

typedef enum {
  kDtAonTimerIrqTypeWkupTimerExpired = 0,
  kDtAonTimerIrqTypeWdogTimerBark = 1,
  kDtAonTimerIrqTypeCount = 2,
} dt_aon_timer_irq_type_t;

typedef enum {
  kDtAonTimerClockClk = 0,
  kDtAonTimerClockAon = 1,
  kDtAonTimerClockCount = 2,
} dt_aon_timer_clock_t;

typedef enum {
  kDtAonTimerPinctrlInputCount = 0,
  kDtAonTimerPinctrlOutputCount = 0,
} dt_aon_timer_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_AON_TIMER_H_
