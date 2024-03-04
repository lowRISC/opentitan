// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SRAM_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SRAM_CTRL_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtSramCtrlRegBlockRegs = 0,
  kDtSramCtrlRegBlockRam = 1,
  kDtSramCtrlRegBlockCount = 2,
} dt_sram_ctrl_reg_block_t;

typedef enum {
  kDtSramCtrlClockClk = 0,
  kDtSramCtrlClockOtp = 1,
  kDtSramCtrlClockCount = 2,
} dt_sram_ctrl_clock_t;

typedef enum {
  kDtSramCtrlPinctrlInputCount = 0,
  kDtSramCtrlPinctrlOutputCount = 0,
} dt_sram_ctrl_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SRAM_CTRL_H_
