// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_csrng.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_csrng

typedef struct dt_device_csrng {
  int32_t id;
  uintptr_t reg_addr;
  int32_t irq[kDtCsrngIrqTypeCount];
} dt_device_csrng_t;

static const dt_device_csrng_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                      \
  [inst] = {                                                       \
      .id = DT_INST_DEP_ORD(inst),                                 \
      .reg_addr = DT_INST_REG_ADDR(inst),                          \
      .irq =                                                       \
          {                                                        \
              [kDtCsrngIrqCsCmdReqDone] =                          \
                  DT_INST_IRQ_BY_NAME(inst, cs_cmd_req_done, irq), \
              [kDtCsrngIrqCsEntropyReq] =                          \
                  DT_INST_IRQ_BY_NAME(inst, cs_entropy_req, irq),  \
              [kDtCsrngIrqCsHwInstExc] =                           \
                  DT_INST_IRQ_BY_NAME(inst, cs_hw_inst_exc, irq),  \
              [kDtCsrngIrqCsFatalErr] =                            \
                  DT_INST_IRQ_BY_NAME(inst, cs_fatal_err, irq),    \
          },                                                       \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_csrng_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_csrng_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_csrng_reg_addr(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].reg_addr;
  }
  return 0;
}

int32_t dt_csrng_irq_id(uint32_t dev_idx, dt_csrng_irq_type_t irq_type) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      irq_type < kDtCsrngIrqTypeCount) {
    return dev[dev_idx].irq[irq_type];
  }
  return -1;
}
