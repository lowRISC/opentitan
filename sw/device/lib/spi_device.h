// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_SPI_DEVICE_H_

#include <stdint.h>

/**
 * Init SPI Device
 *
 * Configure registers, RXF_ADDR, TXF_ADDR, CTRL.TIMER_V
 */
void spid_init(void);

/**
 * Send data over SPI
 *
 * @param data pointer to buffer of uint_8 to send
 * @param len_bytes number of bytes to send
 * @return number of bytes actually sent (<len if no space in the fifo)
 */
uint32_t spid_send(void *data, uint32_t len_bytes);

/**
 * Read the amount of the data from SRAM RX FIFO
 *
 * If remained data is smaller than length, it returns only up to data.
 */
uint32_t spid_read_nb(void *data, uint32_t len);

/**
 * Returns the number of bytes available to read on the RX buffer
 */
uint32_t spid_bytes_available(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_SPI_DEVICE_H_
