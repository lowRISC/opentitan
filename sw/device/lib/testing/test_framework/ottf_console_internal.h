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

/**
 * Configures SPI device GPIO TX indicator pin for `base_print.h` to use.
 *
 * Note that this function will save `gpio` in a global variable, so the
 * pointer must have static storage duration.
 *
 * @param gpio The GPIO handle to use for the SPI console TX indicator pin.
 * @param tx_indicator_pin The GPIO pin to use for the SPI console TX indicator.
 */
void base_spi_device_set_gpio_tx_indicator(dif_gpio_t *gpio,
                                           dif_gpio_pin_t tx_indicator_pin);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_INTERNAL_H_
