// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_PINMUX_H_
#define OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_PINMUX_H_

#include "sw/device/lib/devicetables/dt.h"
#include <stdint.h>

typedef enum {
  kDtPinmuxRegBlockCore = 0,
  kDtPinmuxRegBlockCount = 1,
} dt_pinmux_reg_block_t;

typedef enum {
  kDtPinmuxClockClk = 0,
  kDtPinmuxClockAon = 1,
  kDtPinmuxClockCount = 2,
} dt_pinmux_clock_t;

typedef enum {
  kDtPinmuxPinctrlInputCount = 0,
  kDtPinmuxPinctrlOutputCount = 0,
} dt_pinmux_pinctrl_t;

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_PINMUX_H_
