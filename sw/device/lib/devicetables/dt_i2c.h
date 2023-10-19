// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_I2C_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_I2C_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtI2cRegBlockCore = 0,
  kDtI2cRegBlockCount = 1,
} dt_i2c_reg_block_t;

typedef enum {
  kDtI2cIrqTypeFmtThreshold = 0,
  kDtI2cIrqTypeRxThreshold = 1,
  kDtI2cIrqTypeAcqThreshold = 2,
  kDtI2cIrqTypeRxOverflow = 3,
  kDtI2cIrqTypeNak = 4,
  kDtI2cIrqTypeSclInterference = 5,
  kDtI2cIrqTypeSdaInterference = 6,
  kDtI2cIrqTypeStretchTimeout = 7,
  kDtI2cIrqTypeSdaUnstable = 8,
  kDtI2cIrqTypeCmdComplete = 9,
  kDtI2cIrqTypeTxStretch = 10,
  kDtI2cIrqTypeTxThreshold = 11,
  kDtI2cIrqTypeAcqFull = 12,
  kDtI2cIrqTypeUnexpStop = 13,
  kDtI2cIrqTypeHostTimeout = 14,
  kDtI2cIrqTypeCount = 15,
} dt_i2c_irq_type_t;

typedef enum {
  kDtI2cClockClk = 0,
  kDtI2cClockCount = 1,
} dt_i2c_clock_t;

typedef enum {
  kDtI2cPinctrlInoutSda = 0,
  kDtI2cPinctrlInoutScl = 1,
  kDtI2cPinctrlInputCount = 2,
  kDtI2cPinctrlOutputCount = 2,
} dt_i2c_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_I2C_H_
