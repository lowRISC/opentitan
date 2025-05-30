// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_INTERNAL_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_INTERNAL_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"

#include "spi_device_regs.h"  // Generated.

// Defined in ottf_console.c
extern dif_gpio_t ottf_console_gpio;
extern dif_pinmux_t ottf_console_pinmux;

/**
 * SPI console buffer management constants.
 */
enum {
  kSpiDeviceReadBufferSizeBytes =
      SPI_DEVICE_PARAM_SRAM_READ_BUFFER_DEPTH * sizeof(uint32_t),
  kSpiDeviceFrameHeaderSizeBytes = 12,
  kSpiDeviceBufferPreservedSizeBytes = kSpiDeviceFrameHeaderSizeBytes,
  kSpiDeviceMaxFramePayloadSizeBytes = kSpiDeviceReadBufferSizeBytes -
                                       kSpiDeviceFrameHeaderSizeBytes -
                                       kSpiDeviceBufferPreservedSizeBytes - 4,
  kSpiDeviceFrameMagicNumber = 0xa5a5beef,
};

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_INTERNAL_H_
