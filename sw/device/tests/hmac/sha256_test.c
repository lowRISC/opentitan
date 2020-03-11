// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/base/print.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/hw_sha256.h"
#include "sw/device/lib/uart.h"

static const size_t kDataLen = 142;
static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static const uint32_t kExpectedDigest[8] = {0xdc96c23d, 0xaf36e268, 0xcb68ff71,
                                            0xe92f76e2, 0xb8a8379d, 0x426dc745,
                                            0x19f5cff7, 0x4ec9c6d6};

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);
  LOG_INFO("Running SHA256 test");

  uint32_t digest[8];
  hw_SHA256_hash(kData, kDataLen, (uint8_t *)digest);

  bool has_error = false;
  for (uint32_t i = 0; i < 8; i++) {
    if (digest[i] != kExpectedDigest[i]) {
      flash_write_scratch_reg(digest[i]);
      has_error = true;
      break;
    }
  }

  if (has_error) {
    uart_send_str("FAIL!\r\n");
  } else {
    uart_send_str("PASS!\r\n");
  }

  return 0;
}
