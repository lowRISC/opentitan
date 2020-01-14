// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_UART_H_
#define OPENTITAN_SW_DEVICE_LIB_UART_H_

#include <stdint.h>

void uart_send_char(char c);

/**
 * Send unsigned int over UART
 */
void uart_send_uint(uint32_t n, int size);
void uart_init(unsigned int baud);

/**
 * Send a NULL-terminated string over UART
 */
void uart_send_str(char *str);

/**
 * Receive a single character from UART
 *
 * @param c received character, caller-allocated
 * @return 0 on success, -1 if no data is available
 */
int uart_rcv_char(char *c);

#endif  // OPENTITAN_SW_DEVICE_LIB_UART_H_
