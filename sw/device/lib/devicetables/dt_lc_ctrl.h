// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_LC_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_LC_CTRL_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtLcCtrlRegBlockCore = 0,
  kDtLcCtrlRegBlockCount = 1,
} dt_lc_ctrl_reg_block_t;

typedef enum {
  kDtLcCtrlClockClk = 0,
  kDtLcCtrlClockKmac = 1,
  kDtLcCtrlClockCount = 2,
} dt_lc_ctrl_clock_t;

typedef enum {
  kDtLcCtrlPinctrlInputCount = 0,
  kDtLcCtrlPinctrlOutputCount = 0,
} dt_lc_ctrl_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_LC_CTRL_H_
