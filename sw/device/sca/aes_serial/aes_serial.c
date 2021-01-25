// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/sca/aes_serial/sca.h"

// This program implements the ChipWhisperer simple serial protocol version 1.1.
// Only set key ('k'), encrypt ('p') and version ('v') commands are implemented.
// Encryption is done in AES-ECB-128 mode.
// See https://wiki.newae.com/SimpleSerial for details.

enum {
  kAesKeyLength = 16,
  /**
   * Number of cycles (at `kClockFreqCpuHz`) that Ibex should sleep to minimize
   * noise during AES operations. Caution: This number should be chosen to
   * provide enough time. Otherwise, Ibex might wake up while AES is still busy
   * and disturb the capture. Currently, we use a start trigger delay of 40
   * clock cycles and the scope captures 18 clock cycles at kClockFreqCpuHz (180
   * samples). The latter number will likely increase as we improve the security
   * hardening.
   */
  kIbexAesSleepCycles = 200,
  /**
   * Simple serial protocol version 1.1.
   */
  kSimpleSerialProtocolVersion = 1,
  kUartMaxRxPacketSize = 64,
};

static aes_cfg_t aes_cfg;

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
 * Command handlers.
 *
 * Clients can register handlers for commands 'a'-'z' using
 * `simple_serial_register_handler()` except for 'v' (version), which is handled
 * by this library. This array has an extra element (27) that is initialized in
 * `simple_serial_init()` to point to `simple_serial_unknown_command()` in order
 * to simplify handling of invalid commands in `simple_serial_process_packet()`.
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
 * @param[out] to Value of the nibble.
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
 * @param[out] Buffer for received packet payload.
 * @param data_buf_len Length of the packet payload buffer.
 * @param[out] data_len Received packet payload length.
 */
static void simple_serial_receive_packet(uint8_t *cmd, uint8_t *data,
                                         size_t data_buf_len,
                                         size_t *data_len) {
  while (true) {
    // Read command byte - a single character.
    (void)dif_uart_byte_receive_polled(uart, cmd);
    *data_len = 0;
    // Read payload - a variable length hex encoded string terminated with '\n'.
    do {
      uint8_t hex_byte[2];
      (void)dif_uart_byte_receive_polled(uart, &hex_byte[0]);
      if (hex_byte[0] == '\n') {
        return;
      }
      if (simple_serial_hex_to_bin(hex_byte[0], &hex_byte[0]) !=
          kSimpleSerialOk) {
        break;
      }
      (void)dif_uart_byte_receive_polled(uart, &hex_byte[1]);
      if (simple_serial_hex_to_bin(hex_byte[1], &hex_byte[1]) !=
          kSimpleSerialOk) {
        break;
      }
      if (*data_len == data_buf_len) {
        break;
      }
      data[*data_len] = hex_byte[0] << 4 | hex_byte[1];
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
 * Sends a buffer over UART as a hex encoded string.
 *
 * @param data A buffer
 * @param data_len Size of the buffer.
 */
static void simple_serial_print_hex(const uint8_t *data, size_t data_len) {
  for (int i = 0; i < data_len; ++i) {
    base_printf("%2x", (uint32_t)data[i]);
  }
}

/**
 * Sends a simple serial packet over UART.
 *
 * @param cmd Simple serial command.
 * @param data Packet payload.
 * @param data_len Payload length.
 */
static void simple_serial_send_packet(const uint8_t cmd, const uint8_t *data,
                                      size_t data_len) {
  base_printf("%c", cmd);
  simple_serial_print_hex(data, data_len);
  base_printf("\n");
}

/**
 * Sends a simple serial status packer over UART.
 *
 * @param res Status code.
 */
static void simple_serial_send_status(uint8_t res) {
  simple_serial_send_packet('z', (uint8_t[1]){res}, 1);
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

/**
 * Initializes the data structures used by simple serial.
 *
 * This function also registers the handler for 'v' (version) command.
 *
 * @param uart Handle to an initialized UART device.
 */
static void simple_serial_init(const dif_uart_t *uart_) {
  uart = uart_;

  for (size_t i = 0; i < ARRAYSIZE(handlers); ++i) {
    handlers[i] = simple_serial_unknown_command;
  }
  handlers[simple_serial_get_handler_index('v')] = simple_serial_version;
}

/**
 * Registers a handler for a simple serial command.
 *
 * @param cmd Simple serial command.
 * @param handler Command handler.
 */
static simple_serial_result_t simple_serial_register_handler(
    uint8_t cmd, simple_serial_command_handler handler) {
  if (!simple_serial_is_valid_command(cmd)) {
    return kSimpleSerialError;
  } else if (cmd == 'v') {
    // Cannot register handlers for built-in commands.
    return kSimpleSerialError;
  } else {
    handlers[simple_serial_get_handler_index(cmd)] = handler;
    return kSimpleSerialOk;
  }
}

/**
 * Waits for a simple serial packet and dispatches it to the appropriate
 * handler.
 */
static void simple_serial_process_packet(void) {
  uint8_t cmd;
  uint8_t data[kUartMaxRxPacketSize];
  size_t data_len;
  simple_serial_receive_packet(&cmd, data, ARRAYSIZE(data), &data_len);
  handlers[simple_serial_get_handler_index(cmd)](data, data_len);
}

/**
 * Simple serial 'k' (set key) command handler.
 *
 * This function does not use key shares to simplify side-channel analysis.
 * The key must be `kAesKeySize` bytes long.
 *
 * @param key Key.
 * @param key_len Key length.
 * @return Result of the operation.
 */
static void aes_serial_set_key(const uint8_t *key, size_t key_len) {
  SS_CHECK(key_len == kAesKeyLength);
  aes_key_put(key, (uint8_t[kAesKeyLength]){0}, aes_cfg.key_len);
}

/**
 * Encrypts a plaintext using the AES peripheral.
 *
 * This function uses `sca_call_and_sleep()` from the sca library to put Ibex to
 * sleep in order to minimize noise during captures. The plaintext must be
 * `kAesKeySize` bytes long.
 *
 * @param plaintext Plaintext.
 * @param plaintext_len Length of the plaintext.
 * @return Result of the operation.
 */
static void aes_serial_encrypt(const uint8_t *plaintext, size_t plaintext_len) {
  aes_data_put_wait(plaintext);

  // Start AES operation (this triggers the capture) and go to sleep.
  // Using the SecAesStartTriggerDelay hardware parameter, the AES unit is
  // configured to start operation 40 cycles after receiving the start trigger.
  // This allows Ibex to go to sleep in order to not disturb the capture.
  sca_call_and_sleep(aes_manual_trigger, kIbexAesSleepCycles);
}

/**
 * Simple serial 'p' (encrypt) command handler.
 *
 * Encrypts a `kAesKeySize` bytes long plaintext using the AES peripheral and
 * sends the ciphertext over UART. This function also handles the trigger
 * signal.
 *
 * @param plaintext Plaintext.
 * @param plaintext_len Length of the plaintext.
 */
static void aes_serial_single_encrypt(const uint8_t *plaintext,
                                      size_t plaintext_len) {
  SS_CHECK(plaintext_len == kAesKeyLength);

  sca_set_trigger_high();
  aes_serial_encrypt(plaintext, plaintext_len);
  sca_set_trigger_low();

  uint8_t ciphertext[kAesKeyLength] = {0};
  aes_data_get_wait(ciphertext);
  simple_serial_send_packet('r', ciphertext, ARRAYSIZE(ciphertext));
}

/**
 * Initializes the AES peripheral.
 */
static void init_aes(void) {
  aes_cfg.key_len = kAes128;
  aes_cfg.operation = kAesEnc;
  aes_cfg.mode = kAesEcb;
  aes_cfg.manual_operation = true;
  aes_clear();
  while (!aes_idle()) {
    ;
  }
  aes_init(aes_cfg);
}

/**
 * Main function.
 *
 * Initializes peripherals and processes simple serial packets received over
 * UART.
 */
int main(void) {
  const dif_uart_t *uart;

  sca_init();
  sca_get_uart(&uart);

  simple_serial_init(uart);
  simple_serial_register_handler('k', aes_serial_set_key);
  simple_serial_register_handler('p', aes_serial_single_encrypt);

  init_aes();

  while (true) {
    simple_serial_process_packet();
  }
}
