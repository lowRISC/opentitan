// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_DM_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_DM_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtRvDmRegBlockRegs = 0,
  kDtRvDmRegBlockMem = 1,
  kDtRvDmRegBlockCount = 2,
} dt_rv_dm_reg_block_t;

typedef enum {
  kDtRvDmClockClk = 0,
  kDtRvDmClockCount = 1,
} dt_rv_dm_clock_t;

typedef enum {
  kDtRvDmPinctrlInputCount = 0,
  kDtRvDmPinctrlOutputCount = 0,
} dt_rv_dm_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_DM_H_
