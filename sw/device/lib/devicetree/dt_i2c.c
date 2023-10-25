// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_i2c.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_i2c

typedef struct dt_device_i2c {
  int32_t id;
  uintptr_t reg_addr;
  int32_t irq[kDtI2cIrqTypeCount];
} dt_device_i2c_t;

static const dt_device_i2c_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                                \
  [inst] = {                                                                 \
      .id = DT_INST_DEP_ORD(inst),                                           \
      .reg_addr = DT_INST_REG_ADDR(inst),                                    \
      .irq =                                                                 \
          {                                                                  \
              [kDtI2cIrqFmtThreshold] =                                      \
                  DT_INST_IRQ_BY_NAME(inst, fmt_threshold, irq),             \
              [kDtI2cIrqRxThreshold] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, rx_threshold, irq),              \
              [kDtI2cIrqFmtOverflow] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, fmt_overflow, irq),              \
              [kDtI2cIrqRxOverflow] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, rx_overflow, irq),               \
              [kDtI2cIrqNak] = DT_INST_IRQ_BY_NAME(inst, nak, irq),          \
              [kDtI2cIrqSclInterference] =                                   \
                  DT_INST_IRQ_BY_NAME(inst, scl_interference, irq),          \
              [kDtI2cIrqSdaInterference] =                                   \
                  DT_INST_IRQ_BY_NAME(inst, sda_interference, irq),          \
              [kDtI2cIrqStretchTimeout] =                                    \
                  DT_INST_IRQ_BY_NAME(inst, stretch_timeout, irq),           \
              [kDtI2cIrqSdaUnstable] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, sda_unstable, irq),              \
              [kDtI2cIrqCmdComplete] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, cmd_complete, irq),              \
              [kDtI2cIrqTxStretch] =                                         \
                  DT_INST_IRQ_BY_NAME(inst, tx_stretch, irq),                \
              [kDtI2cIrqTxOverflow] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, tx_overflow, irq),               \
              [kDtI2cIrqAcqFull] = DT_INST_IRQ_BY_NAME(inst, acq_full, irq), \
              [kDtI2cIrqUnexpStop] =                                         \
                  DT_INST_IRQ_BY_NAME(inst, unexp_stop, irq),                \
              [kDtI2cIrqHostTimeout] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, host_timeout, irq),              \
          },                                                                 \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_i2c_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_i2c_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_i2c_reg_addr(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].reg_addr;
  }
  return 0;
}

int32_t dt_i2c_irq_id(uint32_t dev_idx, dt_i2c_irq_type_t irq_type) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      irq_type < kDtI2cIrqTypeCount) {
    return dev[dev_idx].irq[irq_type];
  }
  return -1;
}
