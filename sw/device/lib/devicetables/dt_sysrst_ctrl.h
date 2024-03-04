// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SYSRST_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SYSRST_CTRL_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtSysrstCtrlRegBlockCore = 0,
  kDtSysrstCtrlRegBlockCount = 1,
} dt_sysrst_ctrl_reg_block_t;

typedef enum {
  kDtSysrstCtrlIrqTypeEventDetected = 0,
  kDtSysrstCtrlIrqTypeCount = 1,
} dt_sysrst_ctrl_irq_type_t;

typedef enum {
  kDtSysrstCtrlClockClk = 0,
  kDtSysrstCtrlClockAon = 1,
  kDtSysrstCtrlClockCount = 2,
} dt_sysrst_ctrl_clock_t;

typedef enum {
  kDtSysrstCtrlPinctrlInputAcPresent = 0,
  kDtSysrstCtrlPinctrlInputKey0In = 1,
  kDtSysrstCtrlPinctrlInputKey1In = 2,
  kDtSysrstCtrlPinctrlInputKey2In = 3,
  kDtSysrstCtrlPinctrlInputPwrbIn = 4,
  kDtSysrstCtrlPinctrlInputLidOpen = 5,
  kDtSysrstCtrlPinctrlInoutEcRstL = 6,
  kDtSysrstCtrlPinctrlInoutFlashWpL = 7,
  kDtSysrstCtrlPinctrlOutputBatDisable = 8,
  kDtSysrstCtrlPinctrlOutputKey0Out = 9,
  kDtSysrstCtrlPinctrlOutputKey1Out = 10,
  kDtSysrstCtrlPinctrlOutputKey2Out = 11,
  kDtSysrstCtrlPinctrlOutputPwrbOut = 12,
  kDtSysrstCtrlPinctrlOutputZ3Wakeup = 13,
  kDtSysrstCtrlPinctrlInputCount = 8,
  kDtSysrstCtrlPinctrlOutputCount = 14,
} dt_sysrst_ctrl_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SYSRST_CTRL_H_
