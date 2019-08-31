// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "flash_ctrl.h"
#include "hmac.h"
#include "hmac_regs.h"
#include "uart.h"

typedef union digest {
  uint8_t b[32];
  uint32_t w[8];
} digest_t;

typedef struct test_data {
  uint32_t digest[8];
  char sha_input[512];
} test_data_t;

test_data_t test = {
    {0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2, 0xb8a8379d, 0x426dc745,
     0x19f5cff7, 0x4ec9c6d6},
    "Every one suspects himself of at least one of the cardinal virtues, and "
    "this is mine: I am one of the few honest people that I have ever known"};

int main(int argc, char **argv) {
  uint32_t error = 0;
  digest_t digest;

  uart_init(UART_BAUD_RATE);

  hmac_cfg_t setup = {.mode = Sha256,
                      .input_endian_swap = 1,
                      .digest_endian_swap = 1,
                      .length_lower = 0,
                      .length_upper = 0,
                      .keys = {0}};

  // length in bits
  setup.length_lower = strlen(test.sha_input) << 3;

  hmac_init(setup);

  hmac_write(test.sha_input, strlen(test.sha_input));

  error |= hmac_done(digest.w);

  for (uint32_t i = 0; i < 8; i++) {
    if (digest.w[i] != test.digest[i]) {
      REG32(FLASH_CTRL_SCRATCH(0)) = digest.w[i];
      error++;
      break;
    }
  }

  if (error) {
    uart_send_str("FAIL!\n");
    while (1) {
    }
  } else {
    uart_send_str("PASS!\n");
    __asm__ volatile("wfi;");
  }
}
