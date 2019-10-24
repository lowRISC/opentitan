// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "flash_ctrl.h"
#include "hw_sha256.h"
#include "uart.h"

typedef struct test_data {
  uint32_t digest[8];
  char data[512];
} test_data_t;

test_data_t test = {.digest = {0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2,
                               0xb8a8379d, 0x426dc745, 0x19f5cff7, 0x4ec9c6d6},
                    .data =
                        "Every one suspects himself of at least one of "
                        "the cardinal virtues, and this is mine: I am "
                        "one of the few honest people that I have ever "
                        "known"};

int main(int argc, char **argv) {
  uint32_t error = 0;
  uint32_t digest[8];

  uart_init(UART_BAUD_RATE);
  uart_send_str("Running SHA256 test\r\n");

  hw_SHA256_hash(test.data, strlen(test.data), (uint8_t *)digest);

  for (uint32_t i = 0; i < 8; i++) {
    if (digest[i] != test.digest[i]) {
      flash_write_scratch_reg(digest[i]);
      error++;
      break;
    }
  }

  if (error) {
    uart_send_str("FAIL!\r\n");
  } else {
    uart_send_str("PASS!\r\n");
  }
}
