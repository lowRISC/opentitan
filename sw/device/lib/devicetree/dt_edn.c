// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_edn.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_edn

typedef struct dt_device_edn {
  int32_t id;
  uintptr_t reg_addr;
  int32_t irq[kDtEdnIrqTypeCount];
} dt_device_edn_t;

static const dt_device_edn_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                       \
  [inst] = {                                                        \
      .id = DT_INST_DEP_ORD(inst),                                  \
      .reg_addr = DT_INST_REG_ADDR(inst),                           \
      .irq =                                                        \
          {                                                         \
              [kDtEdnIrqEdnCmdReqDone] =                            \
                  DT_INST_IRQ_BY_NAME(inst, edn_cmd_req_done, irq), \
              [kDtEdnIrqEdnFatalErr] =                              \
                  DT_INST_IRQ_BY_NAME(inst, edn_fatal_err, irq),    \
          },                                                        \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_edn_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_edn_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_edn_reg_addr(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].reg_addr;
  }
  return 0;
}

int32_t dt_edn_irq_id(uint32_t dev_idx, dt_edn_irq_type_t irq_type) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      irq_type < kDtEdnIrqTypeCount) {
    return dev[dev_idx].irq[irq_type];
  }
  return -1;
}
