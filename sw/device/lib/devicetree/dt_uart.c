// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_uart.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_uart

typedef struct dt_device_uart {
  int32_t id;
  uintptr_t reg_addr;
  int32_t irq[kDtUartIrqTypeCount];
} dt_device_uart_t;

static const dt_device_uart_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                                 \
  [inst] = {                                                                  \
      .id = DT_INST_DEP_ORD(inst),                                            \
      .reg_addr = DT_INST_REG_ADDR(inst),                                     \
      .irq =                                                                  \
          {                                                                   \
              [kDtUartIrqTxWatermark] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, tx_watermark, irq),               \
              [kDtUartIrqRxWatermark] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, rx_watermark, irq),               \
              [kDtUartIrqTxEmpty] = DT_INST_IRQ_BY_NAME(inst, tx_empty, irq), \
              [kDtUartIrqRxOverflow] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, rx_overflow, irq),                \
              [kDtUartIrqRxFrameErr] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, rx_frame_err, irq),               \
              [kDtUartIrqRxBreakErr] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, rx_break_err, irq),               \
              [kDtUartIrqRxTimeout] =                                         \
                  DT_INST_IRQ_BY_NAME(inst, rx_timeout, irq),                 \
              [kDtUartIrqRxParityErr] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, rx_parity_err, irq),              \
          },                                                                  \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_uart_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_uart_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_uart_reg_addr(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].reg_addr;
  }
  return 0;
}

int32_t dt_uart_irq_id(uint32_t dev_idx, dt_uart_irq_type_t irq_type) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      irq_type < kDtUartIrqTypeCount) {
    return dev[dev_idx].irq[irq_type];
  }
  return -1;
}
