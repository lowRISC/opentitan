// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_flash_ctrl.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_flash_ctrl

typedef struct dt_device_flash_ctrl {
  int32_t id;
  uintptr_t reg_addr[kDtFlashCtrlRegBlockCount];
  int32_t irq[kDtFlashCtrlIrqTypeCount];
} dt_device_flash_ctrl_t;

static const dt_device_flash_ctrl_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                                  \
  [inst] = {                                                                   \
      .id = DT_INST_DEP_ORD(inst),                                             \
      .reg_addr =                                                              \
          {                                                                    \
              [kDtFlashCtrlRegBlockCore] =                                     \
                  DT_INST_REG_ADDR_BY_NAME(inst, core),                        \
              [kDtFlashCtrlRegBlockPrim] =                                     \
                  DT_INST_REG_ADDR_BY_NAME(inst, prim),                        \
              [kDtFlashCtrlRegBlockMem] = DT_INST_REG_ADDR_BY_NAME(inst, mem), \
          },                                                                   \
      .irq =                                                                   \
          {                                                                    \
              [kDtFlashCtrlIrqProgEmpty] =                                     \
                  DT_INST_IRQ_BY_NAME(inst, prog_empty, irq),                  \
              [kDtFlashCtrlIrqProgLvl] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, prog_lvl, irq),                    \
              [kDtFlashCtrlIrqRdFull] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, rd_full, irq),                     \
              [kDtFlashCtrlIrqRdLvl] = DT_INST_IRQ_BY_NAME(inst, rd_lvl, irq), \
              [kDtFlashCtrlIrqOpDone] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, op_done, irq),                     \
              [kDtFlashCtrlIrqCorrErr] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, corr_err, irq),                    \
          },                                                                   \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_flash_ctrl_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_flash_ctrl_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_flash_ctrl_reg_addr(uint32_t dev_idx,
                                 dt_flash_ctrl_reg_block_t reg_block) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      reg_block < kDtFlashCtrlRegBlockCount) {
    return dev[dev_idx].reg_addr[reg_block];
  }
  return 0;
}

int32_t dt_flash_ctrl_irq_id(uint32_t dev_idx,
                             dt_flash_ctrl_irq_type_t irq_type) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      irq_type < kDtFlashCtrlIrqTypeCount) {
    return dev[dev_idx].irq[irq_type];
  }
  return -1;
}
