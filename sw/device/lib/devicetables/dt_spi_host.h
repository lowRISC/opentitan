// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SPI_HOST_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SPI_HOST_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtSpiHostRegBlockCore = 0,
  kDtSpiHostRegBlockCount = 1,
} dt_spi_host_reg_block_t;

typedef enum {
  kDtSpiHostIrqTypeError = 0,
  kDtSpiHostIrqTypeSpiEvent = 1,
  kDtSpiHostIrqTypeCount = 2,
} dt_spi_host_irq_type_t;

typedef enum {
  kDtSpiHostClockClk = 0,
  kDtSpiHostClockCount = 1,
} dt_spi_host_clock_t;

typedef enum {
  kDtSpiHostPinctrlInoutSd0 = 0,
  kDtSpiHostPinctrlInoutSd1 = 1,
  kDtSpiHostPinctrlInoutSd2 = 2,
  kDtSpiHostPinctrlInoutSd3 = 3,
  kDtSpiHostPinctrlOutputSck = 4,
  kDtSpiHostPinctrlOutputCsb = 5,
  kDtSpiHostPinctrlInputCount = 4,
  kDtSpiHostPinctrlOutputCount = 6,
} dt_spi_host_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_SPI_HOST_H_
