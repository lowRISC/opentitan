// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0`

#ifndef OPENTITAN_SW_DEVICE_BOOT_ROM2_UART_LOG_H_
#define OPENTITAN_SW_DEVICE_BOOT_ROM2_UART_LOG_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_uart.h"

/**
 * UART logging setup, as well as macros built on top of those.
 */

/**
 * Returns a handle to the 0th UART port, for performing low-level UART
 * operations.
 *
 * Prefer to use the LOG_* macros, instead.
 *
 * @return a pointer to a UART handle.
 */
dif_uart_t *uart_log_handle(void);

/**
 * Initialize UART, including logging setup.
 *
 * Should only be called once.
 */
void uart_log_init(void);

#endif  // OPENTITAN_SW_DEVICE_BOOT_ROM2_UART_LOG_H_
