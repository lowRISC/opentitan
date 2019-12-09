// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _UART_H_
#define _UART_H_

#include <stdint.h>

#define UART0_BASE_ADDR 0x40000000

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
int uart_rx_empty(void);
int uart_tx_empty(void);
int uart_tx_idle(void);

/**
 * Receive a single character from UART
 *
 * @param c received character, caller-allocated
 * @return 0 on success, -1 if no data is available
 */
int uart_rcv_char(char *c);

#endif
