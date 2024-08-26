// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_UART_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_UART_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
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
void uart_init(uint32_t precalculated_nco);

/**
 * Enable the receiver on the UART.
 */
void uart_enable_receiver(void);

/**
 * Write a single byte to the UART.
 *
 * @param byte Byte to send.
 */
void uart_putchar(uint8_t byte);

/**
 * Read a single byte from the UART.
 *
 * @param timeout_ms How long to wait.
 * @return The character received or -1 if timeout.
 */
int uart_getchar(uint32_t timeout_ms);

/**
 * Write a buffer to the UART.
 *
 * Writes the complete buffer to the UART and wait for transmision to complete.
 *
 * @param data Pointer to buffer to write.
 * @param len Length of the buffer to write.
 */
void uart_write(const void *data, size_t len);

/**
 * Write an unsigned integer as hex to the UART.
 *
 * Note: this function does not block waiting for the transmitter to finish.
 *
 * @param val The value to write to the UART.
 * @param len The length of the value in bytes (1, 2, or 4 bytes).
 * @param after Packed ASCII values to write after the hex value.
 */
void uart_write_hex(uint32_t val, size_t len, uint32_t after);

/**
 * Write an immediate value to the UART a byte at a time.
 *
 * This function is used to print a few imporant user-facing strings
 * from the ROM, but without having to dereference pointers.  The
 * string to be written is encoded as ASCII in an integer in little-endian
 * order (ie: the string is reversed).  A maximum of eight bytes can be printed
 * in this way.  A zero byte in the value terminates the output.
 *
 * Note: this function does not block waiting for the transmitter to finish.
 *
 * @param val The bytes to print.
 */
void uart_write_imm(uint64_t val);

/**
 * Read from the UART into a buffer.
 *
 * Reads up to `len` bytes into a buffer before the timeout.
 *
 * @param data Pointer to buffer to write.
 * @param len Length of the buffer to write.
 * @param timeout_ms The timeout to receive the complete buffer.
 * @return Number of bytes written.
 */
OT_WARN_UNUSED_RESULT
size_t uart_read(uint8_t *data, size_t len, uint32_t timeout_ms);

/**
 * Returns true if UART TX is idle, otherwise returns false.
 *
 * @return Boolean indicating UART TX activity status.
 */
OT_WARN_UNUSED_RESULT
bool uart_tx_idle(void);

/**
 * Detect if a UART break is asserted for a given period of time.
 *
 * UART break must already be asserted upon entry to this function and must
 * remain asserted for the duration of `timeout_ms`.
 *
 * @param timeout_us The time for which break must be asserted.
 * @return kHardenedBoolTrue if break is asserted.
 */
hardened_bool_t uart_break_detect(uint32_t timeout_us);

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
OT_WARN_UNUSED_RESULT
size_t uart_sink(void *uart, const char *data, size_t len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_UART_H_
