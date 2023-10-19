// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_RV_PLIC_H_
#define OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_RV_PLIC_H_

#include "sw/device/lib/devicetables/dt.h"
#include <stdint.h>

typedef enum {
  kDtRvPlicRegBlockCore = 0,
  kDtRvPlicRegBlockCount = 1,
} dt_rv_plic_reg_block_t;

typedef enum {
  kDtRvPlicClockClk = 0,
  kDtRvPlicClockCount = 1,
} dt_rv_plic_clock_t;

typedef enum {
  kDtRvPlicPinctrlInputCount = 0,
  kDtRvPlicPinctrlOutputCount = 0,
} dt_rv_plic_pinctrl_t;

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_RV_PLIC_H_
