// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_OTBN_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_OTBN_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtOtbnRegBlockCore = 0,
  kDtOtbnRegBlockCount = 1,
} dt_otbn_reg_block_t;

typedef enum {
  kDtOtbnIrqTypeDone = 0,
  kDtOtbnIrqTypeCount = 1,
} dt_otbn_irq_type_t;

typedef enum {
  kDtOtbnClockClk = 0,
  kDtOtbnClockEdn = 1,
  kDtOtbnClockOtp = 2,
  kDtOtbnClockCount = 3,
} dt_otbn_clock_t;

typedef enum {
  kDtOtbnPinctrlInputCount = 0,
  kDtOtbnPinctrlOutputCount = 0,
} dt_otbn_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_OTBN_H_
