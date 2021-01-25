// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/sca/aes_serial/sca.h"

// This program implements the ChipWhisperer simple serial protocol version 1.1.
// Only set key ('k'), encrypt ('p') and version ('v') commands are implemented.
// Encryption is done in AES-ECB-128 mode.
// See https://wiki.newae.com/SimpleSerial for details.

enum {
  kAesKeySize = 16,
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
   * UART constants.
   */
  kUartMaxRxSizeText = 128,
  kUartMaxRxSizeBin = 64,
  /**
   * Simple serial protocol version 1.1.
   */
  kSimpleSerialProtocolVersion = 1,
};

static const dif_uart_t *uart;

// Simple serial status codes
typedef enum simple_serial_result {
  kSimpleSerialOk = 0,
  kSimpleSerialError = 1
} simple_serial_result_t;

/** Returns kSimpleSerialError if the condition evaluates to false */
#define SS_CHECK(condition)      \
  do {                           \
    if (!(condition)) {          \
      return kSimpleSerialError; \
    }                            \
  } while (false)

/**
 * Convert `from` binary `to` hex.
 *
 * @param from input value in binary format.
 * @param[out] to   output value in hex format.
 *
 * @return kSimpleSerialOk on success, kSimpleSerialError otherwise.
 */
static simple_serial_result_t hex_value(uint8_t from, uint8_t *to) {
  if (from >= '0' && from <= '9') {
    *to = from - '0';
  } else if (from >= 'A' && from <= 'F') {
    *to = from - 'A' + 10;
  } else if (from >= 'a' && from <= 'f') {
    *to = from - 'a' + 10;
  } else {
    return kSimpleSerialError;
  }
  return kSimpleSerialOk;
}

/**
 * Convert `num` bytes `from` hex `to` binary format.
 *
 * `from` size is expected to by twice as big as `to`.
 *
 * @param from input buffer for hex formatted characters.
 * @param[out] to output buffer for binary.
 * @param num  length of output buffer.
 *
 * @return kSimpleSerialOk on success, kSimpleSerialError otherwise.
 */
static simple_serial_result_t a2b_hex(const uint8_t *from, uint8_t *to,
                                      size_t num) {
  for (int i = 0; i < num; ++i) {
    uint8_t hi, lo;
    if (hex_value(from[i * 2], &hi) || hex_value(from[i * 2 + 1], &lo)) {
      return kSimpleSerialError;
    }
    to[i] = ((hi & 0xFF) << 4) | (lo & 0xFF);
  }
  return kSimpleSerialOk;
}

/**
 * Send simple serial command response via UART.
 *
 * @param cmd_tag  Simple serial command tag.
 * @param data     Response data. Converted to hex format by this function.
 * @param data_len data length.
 */
static void print_cmd_response(const uint8_t cmd_tag, const uint8_t *data,
                               size_t data_len) {
  base_printf("%c", cmd_tag);
  for (int i = 0; i < data_len; ++i) {
    base_printf("%2x", (uint32_t)data[i]);
  }
  base_printf("\n");
}

/**
 * Simple serial set AES key command.
 *
 * @param aes_cfg AES configuration object.
 * @param key     AES key.
 * @param key_len AES key length.
 *
 * @return kSimpleSerialOk on success, kSimpleSerialError otherwise.
 */
static simple_serial_result_t simple_serial_set_key(const aes_cfg_t *aes_cfg,
                                                    const uint8_t *key_share0,
                                                    size_t key_len) {
  // The implementation does not use key shares to simplify AES attacks.
  static const uint8_t kKeyShare1[32] = {0};

  if (key_len != kAesKeySize) {
    return kSimpleSerialError;
  }

  aes_clear();
  while (!aes_idle()) {
    ;
  }
  aes_init(*aes_cfg);

  aes_key_put(key_share0, kKeyShare1, aes_cfg->key_len);
  return kSimpleSerialOk;
}

/*
 * Simple serial trigger AES encryption command.
 *
 * @param aes_cfg        AES configuration object.
 * @param plaintext     plain text to be encrypted.
 * @param plaintext_len plain text length.
 *
 * @return kSimpleSerialOk on success, kSimpleSerialError otherwise.
 */
static simple_serial_result_t simple_serial_trigger_encryption(
    const uint8_t *plaintext, size_t plaintext_len) {
  if (plaintext_len > kUartMaxRxSizeBin) {
    return kSimpleSerialError;
  }

  uint8_t ciphertext[64];
  if (plaintext_len != kAesKeySize) {
    return kSimpleSerialError;
  }

  // Provide input data to AES.
  aes_data_put_wait(plaintext);

  sca_set_trigger_high();

  // Start AES operation (this triggers the capture) and go to sleep.
  // Using the SecAesStartTriggerDelay hardware parameter, the AES unit is
  // configured to start operation 40 cycles after receiving the start trigger.
  // This allows Ibex to go to sleep in order to not disturb the capture.
  sca_call_and_sleep(aes_manual_trigger, kIbexAesSleepCycles);

  sca_set_trigger_low();

  // Retrieve output data from AES.
  aes_data_get_wait(ciphertext);

  print_cmd_response('r', ciphertext, plaintext_len);
  return kSimpleSerialOk;
}

/**
 * Handle simple serial command.
 *
 * @param aes_cfg AES configuration object.
 * @param cmd     input command buffer.
 * @param cmd_len number of characters set in input buffer.
 */
static void simple_serial_handle_command(const aes_cfg_t *aes_cfg,
                                         const uint8_t *cmd, size_t cmd_len) {
  // Data length is half the size of the hex encoded string.
  const size_t data_len = cmd_len >> 1;
  if (data_len >= kUartMaxRxSizeBin) {
    return;
  }
  uint8_t data[64] = {0};

  // The simple serial protocol does not expect return status codes for invalid
  // data, thus it is ok to return early.
  if (a2b_hex(&cmd[1], data, data_len) == kSimpleSerialError) {
    return;
  }

  if (cmd[0] == 'v') {
    print_cmd_response('z', (uint8_t[1]){kSimpleSerialProtocolVersion},
                       /*data_len=*/1);
    return;
  }

  simple_serial_result_t result = kSimpleSerialOk;
  switch (cmd[0]) {
    case 'k':
      result = simple_serial_set_key(aes_cfg, data, data_len);
      break;
    case 'p':
      result = simple_serial_trigger_encryption(data, data_len);
      break;
    default:
      // Unknown command.
      result = kSimpleSerialError;
  }

  // This protocol version expects a 1 byte return status.
  print_cmd_response('z', (const uint8_t *)&result, /*data_len=*/1);
}

int main(void) {
  sca_init();
  sca_get_uart(&uart);

  aes_cfg_t aes_cfg;
  aes_cfg.key_len = kAes128;
  aes_cfg.operation = kAesEnc;
  aes_cfg.mode = kAesEcb;
  aes_cfg.manual_operation = true;

  uint8_t text[128] = {0};
  size_t pos = 0;
  while (true) {
    size_t chars_read;
    if (dif_uart_bytes_receive(uart, 1, (uint8_t *)&text[pos], &chars_read) !=
            kDifUartOk ||
        chars_read == 0) {
      usleep(50);
      continue;
    }
    if (text[pos] == '\n' || text[pos] == '\r') {
      // Continue to override line feed (\n) or carriage return (\r). This
      // way we don't pass empty lines to the handle_command function.
      if (pos != 0) {
        simple_serial_handle_command(&aes_cfg, text, pos - 1);
      }
      // Reset `pos` for the next command.
      pos = 0;
    } else {
      // Going over the maxium buffer size will result in corrupting the input
      // buffer. This is okay in this case since we control the script used
      // to drive the UART input.
      pos = (pos + 1) % kUartMaxRxSizeText;
    }
  }
}
