// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_PATTGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_PATTGEN_H_

#include <stdint.h>

typedef enum {
  kDtPattgenIrqDoneCh0 = 0,
  kDtPattgenIrqDoneCh1,
  kDtPattgenIrqTypeCount,
} dt_pattgen_irq_type_t;

extern uint32_t dt_pattgen_num_devices(void);
extern int32_t dt_pattgen_device_id(uint32_t dev_idx);
extern uintptr_t dt_pattgen_reg_addr(uint32_t dev_idx);
extern int32_t dt_pattgen_irq_id(uint32_t dev_idx,
                                 dt_pattgen_irq_type_t irq_type);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_PATTGEN_H_
