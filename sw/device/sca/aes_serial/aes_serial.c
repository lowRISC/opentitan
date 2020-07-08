// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/rv_timer.h"
#include "sw/device/lib/uart.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_gpio_t gpio;

// Test buffer maximum buffer sizes
#define MAX_LENGTH_TEXT 128
#define MAX_LENGTH_BIN (MAX_LENGTH_TEXT / 2)

// AES Configuration parameters. These values must match the test driving
// side.
#define AES_BLOCK_SIZE 16
#define AES_KEY_SIZE 16
#define AES_EXEC_COUNTER_CYCLES 10

// Simple serial status codes
#define SIMPLE_SERIAL_OK 0
#define SIMPLE_SERIAL_ERROR 1

// Simple serial protocol version 1.1
#define SIMPLE_PROTOCOL_VERSION 1

// GPIO trigger values
#define GPIO_SET_TRIGGER_HIGH 0x08200
#define GPIO_SET_TRIGGER_LOW 0x00000

// TODO: Switch to rv_timer dif.
// Timer comparator value. Used by interrupt.
static volatile uint64_t timer_cmp = AES_EXEC_COUNTER_CYCLES;

static const uint32_t hart = (uint32_t)kTopEarlgreyPlicTargetIbex0;

/**
 * Convert `from` binary `to` hex.
 *
 * @param from input value in binary format.
 * @param to   output value in hex format.
 *
 * @return SIMPLE_SERIAL_OK on success, SIMPLE_SERIAL_ERROR otherwise.
 */
static uint8_t hex_value(char from, char *to) {
  if (from >= '0' && from <= '9') {
    *to = from - '0';
  } else if (from >= 'A' && from <= 'F') {
    *to = from - 'A' + 10;
  } else if (from >= 'a' && from <= 'f') {
    *to = from - 'a' + 10;
  } else {
    return SIMPLE_SERIAL_ERROR;
  }
  return SIMPLE_SERIAL_OK;
}

/**
 * Convert `num` bytes `from` hex `to` binary format.
 *
 * `from` size is expected to by twice as big as `to`.
 *
 * @param from input buffer for hex formatted characters.
 * @param to   output binary buffer.
 * @param num  number of characters in output buffer.
 *
 * @return SIMPLE_SERIAL_OK on success, SIMPLE_SERIAL_ERROR otherwise.
 */
static uint8_t a2b_hex(const char *from, char *to, size_t num) {
  for (int i = 0; i < num; ++i) {
    char hi, lo;
    if (hex_value(from[i * 2], &hi) || hex_value(from[i * 2 + 1], &lo)) {
      return SIMPLE_SERIAL_ERROR;
    }
    to[i] = ((hi & 0xFF) << 4) | (lo & 0xFF);
  }
  return SIMPLE_SERIAL_OK;
}

/**
 * Send `data` to UART in hex byte format.
 */
static void print_hex_buffer(const char *data, size_t data_len) {
  static const char b2a_hex_values[16] = {'0', '1', '2', '3', '4', '5',
                                          '6', '7', '8', '9', 'A', 'B',
                                          'C', 'D', 'E', 'F'};
  for (int i = 0; i < data_len; ++i) {
    uart_send_char(b2a_hex_values[data[i] >> 4]);
    uart_send_char(b2a_hex_values[data[i] & 0xF]);
  }
}

/**
 * Send simple serial command response via UART.
 *
 * @param cmd_tag  Simple serial command tag.
 * @param data     Response data. Converted to hex format by this function.
 * @param data_len data length.
 */
static void print_cmd_response(const char cmd_tag, const char *data,
                               size_t data_len) {
  uart_send_char(cmd_tag);
  print_hex_buffer(data, data_len);
  uart_send_char('\n');
}

/**
 * Return number of AES blocks from `plain_text_len`.
 */
static size_t get_num_blocks(size_t plain_text_len) {
  size_t num_blocks = plain_text_len / AES_BLOCK_SIZE;
  if ((plain_text_len - (num_blocks * AES_BLOCK_SIZE)) > 0) {
    ++num_blocks;
  }
  return num_blocks;
}

/**
 * Simple serial set AES key command.
 *
 * @param aes_cfg AES configuration object.
 * @param key     AES key.
 * @param key_len AES key length.
 *
 * @return SIMPLE_SERIAL_OK on success, SIMPLE_SERIAL_ERROR otherwise.
 */
static uint8_t simple_serial_set_key(const aes_cfg_t *aes_cfg, const char *key,
                                     size_t key_len) {
  if (key_len != AES_KEY_SIZE) {
    return SIMPLE_SERIAL_ERROR;
  }
  aes_clear();
  while (!aes_idle()) {
    ;
  }
  aes_key_put((const void *)key, aes_cfg->key_len);
  aes_init(*aes_cfg);
  return SIMPLE_SERIAL_OK;
}

/*
 * Simple serial trigger AES encryption command.
 *
 * @param aes_cfg        AES configuration object.
 * @param plain_text     plain text to be encrypted.
 * @param plain_text_len plain text length.
 *
 * @return SIMPLE_SERIAL_OK on success, SIMPLE_SERIAL_ERROR otherwise.
 */
static uint8_t simple_serial_trigger_encryption(const aes_cfg_t *aes_cfg,
                                                const char *plain_text,
                                                size_t plain_text_len) {
  if (plain_text_len > MAX_LENGTH_BIN) {
    return SIMPLE_SERIAL_ERROR;
  }

  char cipher_text[MAX_LENGTH_BIN];
  size_t num_blocks = get_num_blocks(plain_text_len);
  if (num_blocks != 1) {
    return SIMPLE_SERIAL_ERROR;
  }

  // start timer to wake up Ibex after AES is done.
  rv_timer_set_cmp(hart, timer_cmp);
  rv_timer_ctrl(hart, true);

  aes_data_put_wait(plain_text);
  if (dif_gpio_all_write(&gpio, GPIO_SET_TRIGGER_HIGH) != kDifGpioOk) {
    return SIMPLE_SERIAL_ERROR;
  }
  aes_manual_trigger();
  wait_for_interrupt();
  if (dif_gpio_all_write(&gpio, GPIO_SET_TRIGGER_LOW) != kDifGpioOk) {
    return SIMPLE_SERIAL_ERROR;
  }
  aes_data_get_wait(cipher_text);

  print_cmd_response('r', cipher_text, plain_text_len);
  return SIMPLE_SERIAL_OK;
}

/**
 * Handle simple seial command.
 *
 * @param aes_cfg AES configuration object.
 * @param cmd     input command buffer.
 * @param cmd_len number of characters set in input buffer.
 */
static void simple_serial_handle_command(const aes_cfg_t *aes_cfg,
                                         const char *cmd, size_t cmd_len) {
  char data[MAX_LENGTH_BIN] = {0};

  // Data length is half the size of the hex encoded string.
  const size_t data_len = cmd_len >> 1;
  if (data_len >= MAX_LENGTH_BIN) {
    return;
  }

  // The simple serial protocol does not expect return status codes for invalid
  // data, thus it is ok to return early.
  if (a2b_hex(&cmd[1], data, data_len)) {
    return;
  }

  uint8_t result = SIMPLE_SERIAL_OK;
  switch (cmd[0]) {
    case 'k':
      result = simple_serial_set_key(aes_cfg, data, data_len);
      break;
    case 'p':
      result = simple_serial_trigger_encryption(aes_cfg, data, data_len);
      break;
    case 'v':
      result = SIMPLE_PROTOCOL_VERSION;
      break;
    default:;
  }
  print_cmd_response('z', (const char *)&result, /*data_len=*/1);
}

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);
  pinmux_init();

  irq_global_ctrl(true);
  irq_timer_ctrl(true);
  rv_timer_intr_enable(hart, true);
  rv_timer_set_us_tick(hart);

  dif_gpio_config_t gpio_config = {.base_addr =
                                       mmio_region_from_addr(0x40010000)};

  if (dif_gpio_init(&gpio_config, &gpio) != kDifGpioOk) {
    uart_send_str("Fatal error: Unable to initialize GPIO DIF.\r\n");
    abort();
  }

  // Enable GPIO 9 and 15 as output.
  if (dif_gpio_output_mode_all_set(&gpio, 0x08200) != kDifGpioOk) {
    uart_send_str("Fatal error: Unable to configure GPIO output pins.\r\n");
    abort();
  }

  if (dif_gpio_all_write(&gpio, GPIO_SET_TRIGGER_LOW) != kDifGpioOk) {
    uart_send_str("Fatal error: Unable to set GPIO output pins.\r\n");
    abort();
  }

  aes_cfg_t aes_cfg;
  aes_cfg.key_len = kAes128;
  aes_cfg.operation = kAesEnc;
  aes_cfg.mode = kAesEcb;
  aes_cfg.manual_operation = true;

  char text[MAX_LENGTH_TEXT] = {0};
  size_t pos = 0;
  while (true) {
    if (uart_rcv_char(&text[pos]) == -1) {
      usleep(50);
      continue;
    }
    if (text[pos] == '\n' || text[pos] == '\r') {
      // Continue to override line feed (\n) or carriage return (\r). This
      // way we don't pass empty lines to the handle_command function.
      if (pos == 0) {
        continue;
      }
      simple_serial_handle_command(&aes_cfg, text, pos - 1);
      pos = 0;
    } else {
      // Going over the maxium buffer size will result in corrupting the input
      // buffer. This is okay in this case since we control the script used
      // to drive the UART input.
      pos = (pos + 1) % MAX_LENGTH_TEXT;
    }
  }
}

void handler_irq_timer(void) {
  timer_cmp += AES_EXEC_COUNTER_CYCLES;
  rv_timer_ctrl(hart, false);
  rv_timer_clr_all_intrs();
}
