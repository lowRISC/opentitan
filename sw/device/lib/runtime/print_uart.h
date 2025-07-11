// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_UART_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_UART_H_

#include <stdarg.h>
#include <stddef.h>

#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/print.h"

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
void base_uart_stdout(const dif_uart_t *uart);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_UART_H_
