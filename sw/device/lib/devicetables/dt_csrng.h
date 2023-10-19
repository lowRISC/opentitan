// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_CSRNG_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_CSRNG_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtCsrngRegBlockCore = 0,
  kDtCsrngRegBlockCount = 1,
} dt_csrng_reg_block_t;

typedef enum {
  kDtCsrngIrqTypeCsCmdReqDone = 0,
  kDtCsrngIrqTypeCsEntropyReq = 1,
  kDtCsrngIrqTypeCsHwInstExc = 2,
  kDtCsrngIrqTypeCsFatalErr = 3,
  kDtCsrngIrqTypeCount = 4,
} dt_csrng_irq_type_t;

typedef enum {
  kDtCsrngClockClk = 0,
  kDtCsrngClockCount = 1,
} dt_csrng_clock_t;

typedef enum {
  kDtCsrngPinctrlInputCount = 0,
  kDtCsrngPinctrlOutputCount = 0,
} dt_csrng_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_CSRNG_H_
