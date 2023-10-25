// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_RV_CORE_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_RV_CORE_IBEX_H_

#include <stdint.h>

extern uint32_t dt_rv_core_ibex_num_devices(void);
extern int32_t dt_rv_core_ibex_device_id(uint32_t dev_idx);
extern uintptr_t dt_rv_core_ibex_reg_addr(uint32_t dev_idx);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_RV_CORE_IBEX_H_
