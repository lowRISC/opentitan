// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_I2C_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_I2C_H_

#include <stdint.h>

typedef enum {
  kDtI2cIrqFmtThreshold = 0,
  kDtI2cIrqRxThreshold,
  kDtI2cIrqFmtOverflow,
  kDtI2cIrqRxOverflow,
  kDtI2cIrqNak,
  kDtI2cIrqSclInterference,
  kDtI2cIrqSdaInterference,
  kDtI2cIrqStretchTimeout,
  kDtI2cIrqSdaUnstable,
  kDtI2cIrqCmdComplete,
  kDtI2cIrqTxStretch,
  kDtI2cIrqTxOverflow,
  kDtI2cIrqAcqFull,
  kDtI2cIrqUnexpStop,
  kDtI2cIrqHostTimeout,
  kDtI2cIrqTypeCount,
} dt_i2c_irq_type_t;

extern uint32_t dt_i2c_num_devices(void);
extern int32_t dt_i2c_device_id(uint32_t dev_idx);
extern uintptr_t dt_i2c_reg_addr(uint32_t dev_idx);
extern int32_t dt_i2c_irq_id(uint32_t dev_idx, dt_i2c_irq_type_t irq_type);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_I2C_H_
