// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_KEYMGR_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_KEYMGR_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtKeymgrRegBlockCore = 0,
  kDtKeymgrRegBlockCount = 1,
} dt_keymgr_reg_block_t;

typedef enum {
  kDtKeymgrIrqTypeOpDone = 0,
  kDtKeymgrIrqTypeCount = 1,
} dt_keymgr_irq_type_t;

typedef enum {
  kDtKeymgrClockClk = 0,
  kDtKeymgrClockEdn = 1,
  kDtKeymgrClockCount = 2,
} dt_keymgr_clock_t;

typedef enum {
  kDtKeymgrPinctrlInputCount = 0,
  kDtKeymgrPinctrlOutputCount = 0,
} dt_keymgr_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_KEYMGR_H_
