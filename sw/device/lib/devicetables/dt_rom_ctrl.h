// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ROM_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ROM_CTRL_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtRomCtrlRegBlockRegs = 0,
  kDtRomCtrlRegBlockRom = 1,
  kDtRomCtrlRegBlockCount = 2,
} dt_rom_ctrl_reg_block_t;

typedef enum {
  kDtRomCtrlClockClk = 0,
  kDtRomCtrlClockCount = 1,
} dt_rom_ctrl_clock_t;

typedef enum {
  kDtRomCtrlPinctrlInputCount = 0,
  kDtRomCtrlPinctrlOutputCount = 0,
} dt_rom_ctrl_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ROM_CTRL_H_
