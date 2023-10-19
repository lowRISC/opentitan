// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_CLKMGR_H_
#define OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_CLKMGR_H_

#include "sw/device/lib/devicetables/dt.h"
#include <stdint.h>

typedef enum {
  kDtClkmgrRegBlockCore = 0,
  kDtClkmgrRegBlockCount = 1,
} dt_clkmgr_reg_block_t;

typedef enum {
  kDtClkmgrClockClk = 0,
  kDtClkmgrClockMain = 1,
  kDtClkmgrClockIo = 2,
  kDtClkmgrClockUsb = 3,
  kDtClkmgrClockAon = 4,
  kDtClkmgrClockCount = 5,
} dt_clkmgr_clock_t;

typedef enum {
  kDtClkmgrPinctrlInputCount = 0,
  kDtClkmgrPinctrlOutputCount = 0,
} dt_clkmgr_pinctrl_t;

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_CLKMGR_H_
