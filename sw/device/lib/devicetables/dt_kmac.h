// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_KMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_KMAC_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtKmacRegBlockCore = 0,
  kDtKmacRegBlockCount = 1,
} dt_kmac_reg_block_t;

typedef enum {
  kDtKmacIrqTypeKmacDone = 0,
  kDtKmacIrqTypeFifoEmpty = 1,
  kDtKmacIrqTypeKmacErr = 2,
  kDtKmacIrqTypeCount = 3,
} dt_kmac_irq_type_t;

typedef enum {
  kDtKmacClockClk = 0,
  kDtKmacClockEdn = 1,
  kDtKmacClockCount = 2,
} dt_kmac_clock_t;

typedef enum {
  kDtKmacPinctrlInputCount = 0,
  kDtKmacPinctrlOutputCount = 0,
} dt_kmac_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_KMAC_H_
