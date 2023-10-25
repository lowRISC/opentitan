// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt_spi_device.h"

#include <zephyr/devicetree.h>

#define DT_DRV_COMPAT lowrisc_spi_device

typedef struct dt_device_spi_device {
  int32_t id;
  uintptr_t reg_addr;
  int32_t irq[kDtSpiDeviceIrqTypeCount];
} dt_device_spi_device_t;

static const dt_device_spi_device_t dev[] = {
#define DT_DEVICE_ENTRY(inst)                                               \
  [inst] = {                                                                \
      .id = DT_INST_DEP_ORD(inst),                                          \
      .reg_addr = DT_INST_REG_ADDR(inst),                                   \
      .irq =                                                                \
          {                                                                 \
              [kDtSpiDeviceIrqGenericRxFull] =                              \
                  DT_INST_IRQ_BY_NAME(inst, generic_rx_full, irq),          \
              [kDtSpiDeviceIrqGenericRxWatermark] =                         \
                  DT_INST_IRQ_BY_NAME(inst, generic_rx_watermark, irq),     \
              [kDtSpiDeviceIrqGenericTxWatermark] =                         \
                  DT_INST_IRQ_BY_NAME(inst, generic_tx_watermark, irq),     \
              [kDtSpiDeviceIrqGenericRxError] =                             \
                  DT_INST_IRQ_BY_NAME(inst, generic_rx_error, irq),         \
              [kDtSpiDeviceIrqGenericRxOverflow] =                          \
                  DT_INST_IRQ_BY_NAME(inst, generic_rx_overflow, irq),      \
              [kDtSpiDeviceIrqGenericTxUnderflow] =                         \
                  DT_INST_IRQ_BY_NAME(inst, generic_tx_underflow, irq),     \
              [kDtSpiDeviceIrqUploadCmdfifoNotEmpty] =                      \
                  DT_INST_IRQ_BY_NAME(inst, upload_cmdfifo_not_empty, irq), \
              [kDtSpiDeviceIrqUploadPayloadNotEmpty] =                      \
                  DT_INST_IRQ_BY_NAME(inst, upload_payload_not_empty, irq), \
              [kDtSpiDeviceIrqUploadPayloadOverflow] =                      \
                  DT_INST_IRQ_BY_NAME(inst, upload_payload_overflow, irq),  \
              [kDtSpiDeviceIrqReadbufWatermark] =                           \
                  DT_INST_IRQ_BY_NAME(inst, readbuf_watermark, irq),        \
              [kDtSpiDeviceIrqReadbufFlip] =                                \
                  DT_INST_IRQ_BY_NAME(inst, readbuf_flip, irq),             \
              [kDtSpiDeviceIrqTpmHeaderNotEmpty] =                          \
                  DT_INST_IRQ_BY_NAME(inst, tpm_header_not_empty, irq),     \
          },                                                                \
  },

    DT_INST_FOREACH_STATUS_OKAY(DT_DEVICE_ENTRY)};

uint32_t dt_spi_device_num_devices(void) {
  return DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT);
}

int32_t dt_spi_device_device_id(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].id;
  }
  return -1;
}

uintptr_t dt_spi_device_reg_addr(uint32_t dev_idx) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT)) {
    return dev[dev_idx].reg_addr;
  }
  return 0;
}

int32_t dt_spi_device_irq_id(uint32_t dev_idx,
                             dt_spi_device_irq_type_t irq_type) {
  if (dev_idx < DT_NUM_INST_STATUS_OKAY(DT_DRV_COMPAT) &&
      irq_type < kDtSpiDeviceIrqTypeCount) {
    return dev[dev_idx].irq[irq_type];
  }
  return -1;
}
