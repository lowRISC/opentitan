// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SCA_LIB_SIMPLE_SERIAL_H_
#define OPENTITAN_SW_DEVICE_SCA_LIB_SIMPLE_SERIAL_H_

#include "sw/device/lib/dif/dif_uart.h"

#include <stddef.h>
#include <stdint.h>

/**
 * @file
 * @brief Simple serial protocol for side-channel analysis.
 *
 * This library implements simple serial protocol version 1.1 and provides
 * built-in handlers for 'v' (version) and 's' (seed PRNG) commands. Clients
 * can implement additional command by registering their handlers using
 * `simple_serial_register_handler()`. See https://wiki.newae.com/SimpleSerial
 * for details on the protocol.
 */

/**
 * Sends an error message over UART if condition evaluates to false.
 */
#define SS_CHECK(condition)                          \
  do {                                               \
    if (!(condition)) {                              \
      simple_serial_send_status(kSimpleSerialError); \
      return;                                        \
    }                                                \
  } while (false)

/**
 * Simple serial status codes.
 */
typedef enum simple_serial_result {
  kSimpleSerialOk = 0,
  kSimpleSerialError = 1,
} simple_serial_result_t;

/**
 * Command handlers must conform to this prototype.
 */
typedef void (*simple_serial_command_handler)(const uint8_t *, size_t);

/**
 * Initializes the data structures used by simple serial.
 *
 * This function also registers handlers for 'v' (version) and 's' (seed PRNG)
 * commands.
 *
 * @param uart Handle to an initialized UART device.
 */
void simple_serial_init(const dif_uart_t *uart);

/**
 * Registers a handler for a simple serial command.
 *
 * Clients cannot register handlers for 'v' (version) and 's' (seed PRNG)
 * commands since these are handled by this library.
 *
 * @param cmd Simple serial command.
 * @param handler Command handler.
 */
simple_serial_result_t simple_serial_register_handler(
    uint8_t cmd, simple_serial_command_handler handler);

/**
 * Waits for a simple serial packet and dispatches it to the appropriate
 * handler.
 */
void simple_serial_process_packet(void);

/**
 * Sends a simple serial packet over UART.
 *
 * @param cmd Simple serial command.
 * @param data Packet payload.
 * @param data_len Payload length.
 */
void simple_serial_send_packet(const uint8_t cmd, const uint8_t *data,
                               size_t data_len);

/**
 * Sends a simple serial status packer over UART.
 *
 * @param res Status code.
 */
void simple_serial_send_status(uint8_t res);

/**
 * Sends a buffer over UART as a hex encoded string.
 *
 * @param data A buffer
 * @param data_len Size of the buffer.
 */
void simple_serial_print_hex(const uint8_t *data, size_t data_len);

#endif  // OPENTITAN_SW_DEVICE_SCA_LIB_SIMPLE_SERIAL_H_
