// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_SPI_DEVICE_H_

#include <stdarg.h>
#include <stddef.h>

#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/runtime/print.h"

/**
 * Returns a function pointer to the spi device sink function.
 */
sink_func_ptr get_spi_device_sink(void);

/**
 * Configures SPI device stdout for `base_print.h` to use.
 *
 * Note that this function will save `spi_device` in a global variable, so the
 * pointer must have static storage duration.
 *
 * @param spi_device The SPI device handle to use for stdout.
 */
void base_spi_device_stdout(const dif_spi_device_handle_t *spi_device);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_SPI_DEVICE_H_
