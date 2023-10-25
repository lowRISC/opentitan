// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_SPI_DEVICE_H_

#include <stdint.h>

typedef enum {
  kDtSpiDeviceIrqGenericRxFull = 0,
  kDtSpiDeviceIrqGenericRxWatermark,
  kDtSpiDeviceIrqGenericTxWatermark,
  kDtSpiDeviceIrqGenericRxError,
  kDtSpiDeviceIrqGenericRxOverflow,
  kDtSpiDeviceIrqGenericTxUnderflow,
  kDtSpiDeviceIrqUploadCmdfifoNotEmpty,
  kDtSpiDeviceIrqUploadPayloadNotEmpty,
  kDtSpiDeviceIrqUploadPayloadOverflow,
  kDtSpiDeviceIrqReadbufWatermark,
  kDtSpiDeviceIrqReadbufFlip,
  kDtSpiDeviceIrqTpmHeaderNotEmpty,
  kDtSpiDeviceIrqTypeCount,
} dt_spi_device_irq_type_t;

extern uint32_t dt_spi_device_num_devices(void);
extern int32_t dt_spi_device_device_id(uint32_t dev_idx);
extern uintptr_t dt_spi_device_reg_addr(uint32_t dev_idx);
extern int32_t dt_spi_device_irq_id(uint32_t dev_idx,
                                    dt_spi_device_irq_type_t irq_type);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_SPI_DEVICE_H_
