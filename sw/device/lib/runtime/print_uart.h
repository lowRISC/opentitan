// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_UART_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_UART_H_

#include "sw/device/lib/dif/dif_uart.h"

/**
 * Configures a minimal stdout UART driver for `print.h` to use.
 *
 * Note that this function will save `uart` in a global variable, so the pointer
 * must have static storage duration. This driver uses
 * `dif_uart_byte_send_polled` to send characters one by one, does not perform
 * flow control and is generally unsafe to use in an interrupt setting.
 *
 * The UART IP and pinmux must have been initialized prior to calling this
 * function.
 *
 * You should not call this function if you are using the ottf console code,
 * instead use `ottf_console_uart_configure`.
 *
 * @param uart The UART handle to use for stdout.
 */
void base_uart_stdout(const dif_uart_t *uart);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_PRINT_UART_H_
