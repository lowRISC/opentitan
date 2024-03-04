// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_TRIAL1_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_TRIAL1_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtTrial1RegBlockCore = 0,
  kDtTrial1RegBlockCount = 1,
} dt_trial1_reg_block_t;

typedef enum {
  kDtTrial1ClockFixed = 0,
  kDtTrial1ClockCount = 1,
} dt_trial1_clock_t;

typedef enum {
  kDtTrial1PinctrlInputCount = 0,
  kDtTrial1PinctrlOutputCount = 0,
} dt_trial1_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_TRIAL1_H_
