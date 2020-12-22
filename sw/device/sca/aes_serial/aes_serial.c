// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// This program implements the ChipWhisperer simple serial protocol version 1.1.
// Only set key ('k'), encrypt ('p') and version ('v') commands are implemented.
// Encryption is done in AES-ECB-128 mode.
// See https://wiki.newae.com/SimpleSerial for details.

static dif_gpio_t gpio;
static dif_rv_timer_t timer;
static dif_uart_t uart;

// UART input maximum buffer sizes
static const uint32_t kMaxInputLengthText = 128;
static const uint32_t kMaxInputLengthBin = 64;

// AES Configuration parameters. These values must match the test driving
// side.
static const uint32_t kAesBlockSize = 16;
static const uint32_t kAesKeySize = 16;

// Simple serial status codes
typedef enum simple_serial_result {
  kSimpleSerialOk = 0,
  kSimpleSerialError = 1
} simple_serial_result_t;

// Simple serial protocol version 1.1
static const uint32_t kSimpleSerialProtocolVersion = 1;

// GPIO capture trigger values
static const uint32_t kGpioCaptureTriggerHigh = 0x08200;
static const uint32_t kGpioCaptureTriggerLow = 0x00000;

// RV Timer settings
static const uint32_t kHart = (uint32_t)kTopEarlgreyPlicTargetIbex0;
static const uint32_t kComparator = 0;
static const uint64_t kDeadline = 200;  // 200 clock cycles at kClockFreqCpuHz
// Caution: This number should be chosen to provide enough time. Otherwise,
// Ibex might wake up while AES is still busy and disturb the capture.
// Currently, we use a start trigger delay of 40 clock cycles and the scope
// captures 18 clock cycles at kClockFreqCpuHz (180 samples). The latter number
// will likely increase as we improve the security hardening.

// TODO: Remove once there is a CHECK version that does not require test
// library dependencies.
#define CHECK(condition, ...)                             \
  do {                                                    \
    if (!(condition)) {                                   \
      /* NOTE: because the condition in this if           \
         statement can be statically determined,          \
         only one of the below string constants           \
         will be included in the final binary.*/          \
      if (GET_NUM_VARIABLE_ARGS(_, ##__VA_ARGS__) == 0) { \
        LOG_ERROR("CHECK-fail: " #condition);             \
      } else {                                            \
        LOG_ERROR("CHECK-fail: " __VA_ARGS__);            \
      }                                                   \
    }                                                     \
  } while (false)

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
static simple_serial_result_t hex_value(char from, char *to) {
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
static simple_serial_result_t a2b_hex(const char *from, char *to, size_t num) {
  for (int i = 0; i < num; ++i) {
    char hi, lo;
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
static void print_cmd_response(const char cmd_tag, const char *data,
                               size_t data_len) {
  base_printf("%c", cmd_tag);
  for (int i = 0; i < data_len; ++i) {
    base_printf("%2x", (uint32_t)data[i]);
  }
  base_printf("\n");
}

/**
 * Return number of AES blocks from `plain_text_len`.
 */
static size_t get_num_blocks(size_t plain_text_len) {
  size_t num_blocks = plain_text_len / kAesBlockSize;
  if ((plain_text_len - (num_blocks * kAesBlockSize)) > 0) {
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
 * @return kSimpleSerialOk on success, kSimpleSerialError otherwise.
 */
static simple_serial_result_t simple_serial_set_key(const aes_cfg_t *aes_cfg,
                                                    const char *key_share0,
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
 * @param plain_text     plain text to be encrypted.
 * @param plain_text_len plain text length.
 *
 * @return kSimpleSerialOk on success, kSimpleSerialError otherwise.
 */
static simple_serial_result_t simple_serial_trigger_encryption(
    const char *plain_text, size_t plain_text_len) {
  if (plain_text_len > kMaxInputLengthBin) {
    return kSimpleSerialError;
  }

  char cipher_text[64];
  size_t num_blocks = get_num_blocks(plain_text_len);
  if (num_blocks != 1) {
    return kSimpleSerialError;
  }

  // Provide input data to AES.
  aes_data_put_wait(plain_text);

  // Arm capture trigger. The actual trigger signal used for capture is a
  // combination (logical AND) of:
  // - GPIO15 enabled here, and
  // - the busy signal of the AES unit. This signal will go high 40 cycles
  //   after aes_manual_trigger() is executed below and remain high until
  //   the operation has finished.
  SS_CHECK(dif_gpio_write_all(&gpio, kGpioCaptureTriggerHigh) == kDifGpioOk);

  // Start timer to wake up Ibex after AES is done.
  uint64_t current_time;
  SS_CHECK(dif_rv_timer_counter_read(&timer, kHart, &current_time) ==
           kDifRvTimerOk);
  SS_CHECK(dif_rv_timer_arm(&timer, kHart, kComparator,
                            current_time + kDeadline) == kDifRvTimerOk);
  SS_CHECK(dif_rv_timer_counter_set_enabled(
               &timer, kHart, kDifRvTimerEnabled) == kDifRvTimerOk);

  // Start AES operation (this triggers the capture) and go to sleep.
  // Using the SecAesStartTriggerDelay hardware parameter, the AES unit is
  // configured to start operation 40 cycles after receiving the start trigger.
  // This allows Ibex to go to sleep in order to not disturb the capture.
  aes_manual_trigger();
  wait_for_interrupt();

  // Disable capture trigger.
  SS_CHECK(dif_gpio_write_all(&gpio, kGpioCaptureTriggerLow) == kDifGpioOk);

  // Retrieve output data from AES.
  aes_data_get_wait(cipher_text);

  print_cmd_response('r', cipher_text, plain_text_len);
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
                                         const char *cmd, size_t cmd_len) {
  // Data length is half the size of the hex encoded string.
  const size_t data_len = cmd_len >> 1;
  if (data_len >= kMaxInputLengthBin) {
    return;
  }
  char data[64] = {0};

  // The simple serial protocol does not expect return status codes for invalid
  // data, thus it is ok to return early.
  if (a2b_hex(&cmd[1], data, data_len) == kSimpleSerialError) {
    return;
  }

  if (cmd[0] == 'v') {
    print_cmd_response('z', (const char *)&kSimpleSerialProtocolVersion,
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
  print_cmd_response('z', (const char *)&result, /*data_len=*/1);
}

int main(int argc, char **argv) {
  CHECK(dif_uart_init(
            (dif_uart_params_t){
                .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART_BASE_ADDR),
            },
            &uart) == kDifUartOk);
  CHECK(dif_uart_configure(&uart, (dif_uart_config_t){
                                      .baudrate = kUartBaudrate,
                                      .clk_freq_hz = kClockFreqPeripheralHz,
                                      .parity_enable = kDifUartToggleDisabled,
                                      .parity = kDifUartParityEven,
                                  }) == kDifUartConfigOk);
  base_uart_stdout(&uart);

  pinmux_init();

  irq_global_ctrl(true);
  irq_timer_ctrl(true);

  CHECK(dif_rv_timer_init(
            mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR),
            (dif_rv_timer_config_t){.hart_count = 1, .comparator_count = 1},
            &timer) == kDifRvTimerOk);
  dif_rv_timer_tick_params_t tick_params;
  CHECK(dif_rv_timer_approximate_tick_params(kClockFreqPeripheralHz,
                                             kClockFreqCpuHz, &tick_params) ==
        kDifRvTimerApproximateTickParamsOk);
  CHECK(dif_rv_timer_set_tick_params(&timer, kHart, tick_params) ==
        kDifRvTimerOk);
  CHECK(dif_rv_timer_irq_enable(&timer, kHart, kComparator,
                                kDifRvTimerEnabled) == kDifRvTimerOk);

  dif_gpio_params_t gpio_params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR)};
  CHECK(dif_gpio_init(gpio_params, &gpio) == kDifGpioOk);
  CHECK(dif_gpio_output_set_enabled_all(&gpio, 0x08200) == kDifGpioOk);
  CHECK(dif_gpio_write_all(&gpio, kGpioCaptureTriggerLow) == kDifGpioOk);

  aes_cfg_t aes_cfg;
  aes_cfg.key_len = kAes128;
  aes_cfg.operation = kAesEnc;
  aes_cfg.mode = kAesEcb;
  aes_cfg.manual_operation = true;

  char text[128] = {0};
  size_t pos = 0;
  while (true) {
    size_t chars_read;
    if (dif_uart_bytes_receive(&uart, 1, (uint8_t *)&text[pos], &chars_read) !=
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
      pos = (pos + 1) % kMaxInputLengthText;
    }
  }
}

void handler_irq_timer(void) {
  bool irq_flag;
  CHECK(dif_rv_timer_irq_get(&timer, kHart, kComparator, &irq_flag) ==
        kDifRvTimerOk);
  CHECK(irq_flag, "Entered IRQ handler but the expected IRQ flag wasn't set!");

  CHECK(dif_rv_timer_counter_set_enabled(&timer, kHart, kDifRvTimerDisabled) ==
        kDifRvTimerOk);
  CHECK(dif_rv_timer_irq_clear(&timer, kHart, kComparator) == kDifRvTimerOk);
}
