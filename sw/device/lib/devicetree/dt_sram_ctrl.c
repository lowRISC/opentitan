// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_sram_ctrl.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_sram_ctrl

typedef struct dt_device_sram_ctrl {
  int32_t id;
  uintptr_t reg_addr[kDtSramCtrlRegBlockCount];
  // sram_ctrl has no IRQs.
} dt_device_sram_ctrl_t;

static const dt_device_sram_ctrl_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                                 \
  [inst] = {                                                                  \
      .id = DT_INST_DEP_ORD(inst),                                            \
      .reg_addr =                                                             \
          {                                                                   \
              [kDtSramCtrlRegBlockRegs] =                                     \
                  DT_INST_REG_ADDR_BY_NAME(inst, regs),                       \
              [kDtSramCtrlRegBlockRam] = DT_INST_REG_ADDR_BY_NAME(inst, ram), \
          },                                                                  \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_sram_ctrl_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_sram_ctrl_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_sram_ctrl_reg_addr(uint32_t dev_idx,
                                dt_sram_ctrl_reg_block_t reg_block) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      reg_block < kDtSramCtrlRegBlockCount) {
    return dev[dev_idx].reg_addr[reg_block];
  }
  return 0;
}
