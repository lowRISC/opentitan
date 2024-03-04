// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_FLASH_CTRL_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtFlashCtrlRegBlockCore = 0,
  kDtFlashCtrlRegBlockPrim = 1,
  kDtFlashCtrlRegBlockMem = 2,
  kDtFlashCtrlRegBlockCount = 3,
} dt_flash_ctrl_reg_block_t;

typedef enum {
  kDtFlashCtrlIrqTypeProgEmpty = 0,
  kDtFlashCtrlIrqTypeProgLvl = 1,
  kDtFlashCtrlIrqTypeRdFull = 2,
  kDtFlashCtrlIrqTypeRdLvl = 3,
  kDtFlashCtrlIrqTypeOpDone = 4,
  kDtFlashCtrlIrqTypeCorrErr = 5,
  kDtFlashCtrlIrqTypeCount = 6,
} dt_flash_ctrl_irq_type_t;

typedef enum {
  kDtFlashCtrlClockClk = 0,
  kDtFlashCtrlClockOtp = 1,
  kDtFlashCtrlClockCount = 2,
} dt_flash_ctrl_clock_t;

typedef enum {
  kDtFlashCtrlPinctrlInputTck = 0,
  kDtFlashCtrlPinctrlInputTms = 1,
  kDtFlashCtrlPinctrlInputTdi = 2,
  kDtFlashCtrlPinctrlOutputTdo = 3,
  kDtFlashCtrlPinctrlInputCount = 3,
  kDtFlashCtrlPinctrlOutputCount = 4,
} dt_flash_ctrl_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_FLASH_CTRL_H_
