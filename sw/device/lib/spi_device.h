// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _SPI_DEVICE_H_
#define _SPI_DEVICE_H_

#include "sw/device/lib/base/types.h"

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
uint32 spid_send(void *data, uint32 len_bytes);

/**
 * Read the amount of the data from SRAM RX FIFO
 *
 * If remained data is smaller than length, it returns only up to data.
 */
uint32 spid_read_nb(void *data, uint32 len);

/**
 * Returns the number of bytes available to read on the RX buffer
 */
uint32 spid_bytes_available(void);

#endif /* _SPI_DEVICE_H_ */
