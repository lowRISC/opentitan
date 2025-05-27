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
 * Returns a function pointer to the uart sink function.
 */
sink_func_ptr get_uart_sink(void);

/**
 * Configures UART stdout for `base_print.h` to use.
 *
 * Note that this function will save `uart` in a global variable, so the pointer
 * must have static storage duration.
 *
 * @param uart The UART handle to use for stdout.
 */
void base_console_uart_stdout(const dif_uart_t *uart);

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

/**
 * Configures SPI device stdout for `base_print.h` to use.
 *
 * Note that this function will save `spi_device` in a global variable, so the
 * pointer must have static storage duration.
 *
 * @param spi_device The SPI device handle to use for stdout.
 */
void base_spi_device_stdout(const dif_spi_device_handle_t *spi_device);

/**
 * Returns a function pointer to the spi device sink function.
 */
sink_func_ptr get_spi_device_sink(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_INTERNAL_H_
