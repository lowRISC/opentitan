// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_RSTMGR_H_
#define OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_RSTMGR_H_

#include "sw/device/lib/devicetables/dt.h"
#include <stdint.h>

typedef enum {
  kDtRstmgrRegBlockCore = 0,
  kDtRstmgrRegBlockCount = 1,
} dt_rstmgr_reg_block_t;

typedef enum {
  kDtRstmgrClockClk = 0,
  kDtRstmgrClockAon = 1,
  kDtRstmgrClockIoDiv4 = 2,
  kDtRstmgrClockMain = 3,
  kDtRstmgrClockIo = 4,
  kDtRstmgrClockIoDiv2 = 5,
  kDtRstmgrClockUsb = 6,
  kDtRstmgrClockPor = 7,
  kDtRstmgrClockCount = 8,
} dt_rstmgr_clock_t;

typedef enum {
  kDtRstmgrPinctrlInputCount = 0,
  kDtRstmgrPinctrlOutputCount = 0,
} dt_rstmgr_pinctrl_t;

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_RSTMGR_H_
