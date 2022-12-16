// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_UART_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_UART_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initialize the UART with the request parameters.
 *
 * @param precalculated_nco NCO value used to set the speed of the UART.
 * @return kErrorOk if successful, else an error code.
 */
rom_error_t uart_init(uint32_t precalculated_nco);

/**
 * Write a single byte to the UART.
 *
 * @param byte Byte to send.
 */
void uart_putchar(uint8_t byte);

/**
 * Write a buffer to the UART.
 *
 * Writes the complete buffer to the UART and wait for transmision to complete.
 *
 * @param data Pointer to buffer to write.
 * @param len Length of the buffer to write.
 * @return Number of bytes written.
 */
size_t uart_write(const uint8_t *data, size_t len);

/**
 * Sink a buffer to the UART.
 *
 * This is a wrapper for uart_write which conforms to the type signature
 * required by the print library.
 *
 * @param uart Pointer a target so satisfy the shape of the sink API.
 * @param data Pointer to buffer to write.
 * @param len Length of the buffer to write.
 * @return Number of bytes written.
 */
size_t uart_sink(void *uart, const char *data, size_t len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_UART_H_
