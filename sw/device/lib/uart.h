// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _UART_H_
#define _UART_H_

#include <stdint.h>

#include "sw/device/lib/common.h"
#include "uart_regs.h"  // Generated.

#define UART0_BASE_ADDR 0x40000000

#define UART_REG_DEF(id, rname) (REG_DEF(UART, id, rname))
#define UART_CTRL(id) (UART_REG_DEF(id, CTRL))
#define UART_FIFO_CTRL(id) (UART_REG_DEF(id, FIFO_CTRL))
#define UART_INTR_ENABLE(id) (UART_REG_DEF(id, INTR_ENABLE))
#define UART_STATUS(id) (UART_REG_DEF(id, STATUS))
#define UART_WDATA(id) (UART_REG_DEF(id, WDATA))
#define UART_RDATA(id) (UART_REG_DEF(id, RDATA))

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
