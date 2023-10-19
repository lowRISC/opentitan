// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SPI_DEVICE_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtSpiDeviceRegBlockCore = 0,
  kDtSpiDeviceRegBlockCount = 1,
} dt_spi_device_reg_block_t;

typedef enum {
  kDtSpiDeviceIrqTypeUploadCmdfifoNotEmpty = 0,
  kDtSpiDeviceIrqTypeUploadPayloadNotEmpty = 1,
  kDtSpiDeviceIrqTypeUploadPayloadOverflow = 2,
  kDtSpiDeviceIrqTypeReadbufWatermark = 3,
  kDtSpiDeviceIrqTypeReadbufFlip = 4,
  kDtSpiDeviceIrqTypeTpmHeaderNotEmpty = 5,
  kDtSpiDeviceIrqTypeTpmRdfifoCmdEnd = 6,
  kDtSpiDeviceIrqTypeTpmRdfifoDrop = 7,
  kDtSpiDeviceIrqTypeCount = 8,
} dt_spi_device_irq_type_t;

typedef enum {
  kDtSpiDeviceClockClk = 0,
  kDtSpiDeviceClockCount = 1,
} dt_spi_device_clock_t;

typedef enum {
  kDtSpiDevicePinctrlInputSck = 0,
  kDtSpiDevicePinctrlInputCsb = 1,
  kDtSpiDevicePinctrlInputTpmCsb = 2,
  kDtSpiDevicePinctrlInoutSd0 = 3,
  kDtSpiDevicePinctrlInoutSd1 = 4,
  kDtSpiDevicePinctrlInoutSd2 = 5,
  kDtSpiDevicePinctrlInoutSd3 = 6,
  kDtSpiDevicePinctrlInputCount = 7,
  kDtSpiDevicePinctrlOutputCount = 7,
} dt_spi_device_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SPI_DEVICE_H_
