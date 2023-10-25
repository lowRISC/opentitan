// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_usbdev.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_usbdev

typedef struct dt_device_usbdev {
  int32_t id;
  uintptr_t reg_addr;
  int32_t irq[kDtUsbdevIrqTypeCount];
} dt_device_usbdev_t;

static const dt_device_usbdev_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                                  \
  [inst] = {                                                                   \
      .id = DT_INST_DEP_ORD(inst),                                             \
      .reg_addr = DT_INST_REG_ADDR(inst),                                      \
      .irq =                                                                   \
          {                                                                    \
              [kDtUsbdevIrqPktReceived] =                                      \
                  DT_INST_IRQ_BY_NAME(inst, pkt_received, irq),                \
              [kDtUsbdevIrqPktSent] =                                          \
                  DT_INST_IRQ_BY_NAME(inst, pkt_sent, irq),                    \
              [kDtUsbdevIrqDisconnected] =                                     \
                  DT_INST_IRQ_BY_NAME(inst, disconnected, irq),                \
              [kDtUsbdevIrqHostLost] =                                         \
                  DT_INST_IRQ_BY_NAME(inst, host_lost, irq),                   \
              [kDtUsbdevIrqLinkReset] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, link_reset, irq),                  \
              [kDtUsbdevIrqLinkSuspend] =                                      \
                  DT_INST_IRQ_BY_NAME(inst, link_suspend, irq),                \
              [kDtUsbdevIrqLinkResume] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, link_resume, irq),                 \
              [kDtUsbdevIrqAvEmpty] =                                          \
                  DT_INST_IRQ_BY_NAME(inst, av_empty, irq),                    \
              [kDtUsbdevIrqRxFull] = DT_INST_IRQ_BY_NAME(inst, rx_full, irq),  \
              [kDtUsbdevIrqAvOverflow] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, av_overflow, irq),                 \
              [kDtUsbdevIrqLinkInErr] =                                        \
                  DT_INST_IRQ_BY_NAME(inst, link_in_err, irq),                 \
              [kDtUsbdevIrqRxCrcErr] =                                         \
                  DT_INST_IRQ_BY_NAME(inst, rx_crc_err, irq),                  \
              [kDtUsbdevIrqRxPidErr] =                                         \
                  DT_INST_IRQ_BY_NAME(inst, rx_pid_err, irq),                  \
              [kDtUsbdevIrqRxBitstuffErr] =                                    \
                  DT_INST_IRQ_BY_NAME(inst, rx_bitstuff_err, irq),             \
              [kDtUsbdevIrqFrame] = DT_INST_IRQ_BY_NAME(inst, frame, irq),     \
              [kDtUsbdevIrqPowered] = DT_INST_IRQ_BY_NAME(inst, powered, irq), \
              [kDtUsbdevIrqLinkOutErr] =                                       \
                  DT_INST_IRQ_BY_NAME(inst, link_out_err, irq),                \
          },                                                                   \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_usbdev_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_usbdev_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_usbdev_reg_addr(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].reg_addr;
  }
  return 0;
}

int32_t dt_usbdev_irq_id(uint32_t dev_idx, dt_usbdev_irq_type_t irq_type) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      irq_type < kDtUsbdevIrqTypeCount) {
    return dev[dev_idx].irq[irq_type];
  }
  return -1;
}
