// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ENTROPY_SRC_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ENTROPY_SRC_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtEntropySrcRegBlockCore = 0,
  kDtEntropySrcRegBlockCount = 1,
} dt_entropy_src_reg_block_t;

typedef enum {
  kDtEntropySrcIrqTypeEsEntropyValid = 0,
  kDtEntropySrcIrqTypeEsHealthTestFailed = 1,
  kDtEntropySrcIrqTypeEsObserveFifoReady = 2,
  kDtEntropySrcIrqTypeEsFatalErr = 3,
  kDtEntropySrcIrqTypeCount = 4,
} dt_entropy_src_irq_type_t;

typedef enum {
  kDtEntropySrcClockClk = 0,
  kDtEntropySrcClockCount = 1,
} dt_entropy_src_clock_t;

typedef enum {
  kDtEntropySrcPinctrlInputCount = 0,
  kDtEntropySrcPinctrlOutputCount = 0,
} dt_entropy_src_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ENTROPY_SRC_H_
