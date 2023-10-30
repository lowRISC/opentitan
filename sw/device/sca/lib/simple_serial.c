// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/sca/lib/simple_serial.h"

#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/ip/uart/dif/dif_uart.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/runtime/print.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

/**
 * Macro for ignoring return values.
 *
 * This is needed because ‘(void)expr;` does not work for gcc.
 */
#define IGNORE_RESULT(expr) \
  if (expr) {               \
  }

enum {
  /**
   * Simple serial protocol version 1.1.
   */
  kSimpleSerialProtocolVersion = 1,
  kUartMaxRxPacketSize = 128,
};

/**
 * Command handlers.
 *
 * Clients can register handlers for commands 'a'-'z' using
 * `simple_serial_register_handler()` except for 'v' (version), 's' (seed
 * PRNG), and 't' (select trigger type) which are handled by this library. This
 * array has an extra element (27) that is initialized in `simple_serial_init()`
 * to point to `simple_serial_unknown_command()` in order to simplify handling
 * of invalid commands in `simple_serial_process_packet()`.
 */
static simple_serial_command_handler handlers[27];
static const dif_uart_t *uart;

static bool simple_serial_is_valid_command(uint8_t cmd) {
  return cmd >= 'a' && cmd <= 'z';
}

/**
 * Converts a hex encoded nibble to binary.
 *
 * @param hex A hex encoded nibble.
 * @param[out] val Value of the nibble.
 *
 * @return Result of the operation.
 */
static simple_serial_result_t simple_serial_hex_to_bin(uint8_t hex,
                                                       uint8_t *val) {
  if (hex >= '0' && hex <= '9') {
    *val = hex - '0';
  } else if (hex >= 'A' && hex <= 'F') {
    *val = hex - 'A' + 10;
  } else if (hex >= 'a' && hex <= 'f') {
    *val = hex - 'a' + 10;
  } else {
    return kSimpleSerialError;
  }
  return kSimpleSerialOk;
}

/**
 * Receives a simple serial packet over UART.
 *
 * Simple serial packets are composed of:
 * - Command: A single byte character,
 * - Payload: A variable length hex encoded string,
 * - Terminator: '\n'.
 *
 * @param[out] cmd Simple serial command.
 * @param[out] data Buffer for received packet payload.
 * @param data_buf_len Length of the packet payload buffer.
 * @param[out] data_len Received packet payload length.
 */
static void simple_serial_receive_packet(uint8_t *cmd, uint8_t *data,
                                         size_t data_buf_len,
                                         size_t *data_len) {
  while (true) {
    // Read command byte - a single character.
    IGNORE_RESULT(dif_uart_byte_receive_polled(uart, cmd));
    if (*cmd == '\n') {
      continue;
    }
    *data_len = 0;
    // Read payload - a variable length hex encoded string terminated with '\n'.
    do {
      uint8_t hex_byte[2];
      IGNORE_RESULT(dif_uart_byte_receive_polled(uart, &hex_byte[0]));
      if (hex_byte[0] == '\n') {
        return;
      }
      if (simple_serial_hex_to_bin(hex_byte[0], &hex_byte[0]) !=
          kSimpleSerialOk) {
        break;
      }
      IGNORE_RESULT(dif_uart_byte_receive_polled(uart, &hex_byte[1]));
      if (simple_serial_hex_to_bin(hex_byte[1], &hex_byte[1]) !=
          kSimpleSerialOk) {
        break;
      }
      if (*data_len == data_buf_len) {
        break;
      }
      data[*data_len] = (uint8_t)(hex_byte[0] << 4) | hex_byte[1];
      ++*data_len;
    } while (true);
  }
}

/**
 * Returns the index of a command's handler in `handlers`.
 *
 * This function returns the index of the last element, which points to
 * `simple_serial_unknown_command(), if the given command is not valid.
 *
 * @param cmd A simple serial command.
 * @return Command handler's index in `handlers`.
 */
static size_t simple_serial_get_handler_index(uint8_t cmd) {
  if (simple_serial_is_valid_command(cmd)) {
    return cmd - 'a';
  } else {
    return ARRAYSIZE(handlers) - 1;
  }
}

/**
 * Simple serial 'v' (version) command handler.
 *
 * Returns the simple serial version that this file implements. This command is
 * useful for checking that the host and the device can communicate properly
 * before starting capturing traces.
 *
 * @param data Received packet payload.
 * @param data_len Payload length.
 */
static void simple_serial_version(const uint8_t *data, size_t data_len) {
  simple_serial_send_status(kSimpleSerialProtocolVersion);
}

/**
 * Simple serial 's' (seed PRNG) command handler.
 *
 * This function only supports 4-byte seeds.
 *
 * @param seed A buffer holding the seed.
 * @param seed_len Seed length.
 */
static void simple_serial_seed_prng(const uint8_t *seed, size_t seed_len) {
  SS_CHECK(seed_len == sizeof(uint32_t));
  prng_seed(read_32(seed));
}

/**
 * Simple serial 't' (select trigger type) command handler.
 *
 * This function only supports 1-byte trigger values.
 *
 * @param trigger A buffer holding the trigger type.
 * @param trigger_len Buffer length.
 */
static void simple_serial_select_trigger_type(const uint8_t *trigger,
                                              size_t trigger_len) {
  SS_CHECK(trigger_len == 1);
  sca_select_trigger_type((sca_trigger_type_t)trigger[0]);
}

/**
 * Handler for uninmplemented simple serial commands.
 *
 * Sends an error packet over UART.
 *
 * @param data Received packet payload
 * @param data_len Payload length.
 */
static void simple_serial_unknown_command(const uint8_t *data,
                                          size_t data_len) {
  simple_serial_send_status(kSimpleSerialError);
}

void simple_serial_init(const dif_uart_t *uart_) {
  uart = uart_;

  for (size_t i = 0; i < ARRAYSIZE(handlers); ++i) {
    handlers[i] = simple_serial_unknown_command;
  }
  handlers[simple_serial_get_handler_index('s')] = simple_serial_seed_prng;
  handlers[simple_serial_get_handler_index('t')] =
      simple_serial_select_trigger_type;
  handlers[simple_serial_get_handler_index('v')] = simple_serial_version;
}

simple_serial_result_t simple_serial_register_handler(
    uint8_t cmd, simple_serial_command_handler handler) {
  if (!simple_serial_is_valid_command(cmd)) {
    return kSimpleSerialError;
  } else if (cmd == 's' || cmd == 't' || cmd == 'v') {
    // Cannot register handlers for built-in commands.
    return kSimpleSerialError;
  } else {
    handlers[simple_serial_get_handler_index(cmd)] = handler;
    return kSimpleSerialOk;
  }
}

void simple_serial_process_packet(void) {
  uint8_t cmd;
  uint8_t data[kUartMaxRxPacketSize];
  size_t data_len;
  simple_serial_receive_packet(&cmd, data, ARRAYSIZE(data), &data_len);
  handlers[simple_serial_get_handler_index(cmd)](data, data_len);
}

void simple_serial_send_packet(const uint8_t cmd, const uint8_t *data,
                               size_t data_len) {
  char buf;
  base_snprintf(&buf, 1, "%c", cmd);
  IGNORE_RESULT(dif_uart_byte_send_polled(uart, buf));
  simple_serial_print_hex(data, data_len);
  base_snprintf(&buf, 1, "\n");
  IGNORE_RESULT(dif_uart_byte_send_polled(uart, buf));
}

void simple_serial_send_status(uint8_t res) {
  simple_serial_send_packet('z', (uint8_t[1]){res}, 1);
}

void simple_serial_print_hex(const uint8_t *data, size_t data_len) {
  char buf[2];
  for (size_t i = 0; i < data_len; ++i) {
    base_snprintf(&buf[0], 2, "%02x", data[i]);
    IGNORE_RESULT(dif_uart_byte_send_polled(uart, buf[0]));
    IGNORE_RESULT(dif_uart_byte_send_polled(uart, buf[1]));
  }
}
