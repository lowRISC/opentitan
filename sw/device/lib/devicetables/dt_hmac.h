// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_HMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_HMAC_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtHmacRegBlockCore = 0,
  kDtHmacRegBlockCount = 1,
} dt_hmac_reg_block_t;

typedef enum {
  kDtHmacIrqTypeHmacDone = 0,
  kDtHmacIrqTypeFifoEmpty = 1,
  kDtHmacIrqTypeHmacErr = 2,
  kDtHmacIrqTypeCount = 3,
} dt_hmac_irq_type_t;

typedef enum {
  kDtHmacClockClk = 0,
  kDtHmacClockCount = 1,
} dt_hmac_clock_t;

typedef enum {
  kDtHmacPinctrlInputCount = 0,
  kDtHmacPinctrlOutputCount = 0,
} dt_hmac_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_HMAC_H_
