// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_CORE_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_CORE_IBEX_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtRvCoreIbexRegBlockCfg = 0,
  kDtRvCoreIbexRegBlockCount = 1,
} dt_rv_core_ibex_reg_block_t;

typedef enum {
  kDtRvCoreIbexClockClk = 0,
  kDtRvCoreIbexClockEdn = 1,
  kDtRvCoreIbexClockEsc = 2,
  kDtRvCoreIbexClockOtp = 3,
  kDtRvCoreIbexClockCount = 4,
} dt_rv_core_ibex_clock_t;

typedef enum {
  kDtRvCoreIbexPinctrlInputCount = 0,
  kDtRvCoreIbexPinctrlOutputCount = 0,
} dt_rv_core_ibex_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_RV_CORE_IBEX_H_
