// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_EDN_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_EDN_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtEdnRegBlockCore = 0,
  kDtEdnRegBlockCount = 1,
} dt_edn_reg_block_t;

typedef enum {
  kDtEdnIrqTypeEdnCmdReqDone = 0,
  kDtEdnIrqTypeEdnFatalErr = 1,
  kDtEdnIrqTypeCount = 2,
} dt_edn_irq_type_t;

typedef enum {
  kDtEdnClockClk = 0,
  kDtEdnClockCount = 1,
} dt_edn_clock_t;

typedef enum {
  kDtEdnPinctrlInputCount = 0,
  kDtEdnPinctrlOutputCount = 0,
} dt_edn_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_EDN_H_
