// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdlib.h>
#include <string.h>

#include "aes.h"
#include "common.h"
#include "uart.h"

// The example below is extracted from
// the Advanced Encryption Standard (AES) FIPS Publication 197 available at
// https://www.nist.gov/publications/advanced-encryption-standard-aes.

static const unsigned char plain_text_1[16] = {
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
    0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff};

static const unsigned char key_32_1[32] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
    0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f};

static const unsigned char cipher_text_gold_32_1[16] = {
    0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf,
    0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89};

int main(int argc, char **argv) {
  uint32_t error = 0;

  aes_idle();

  unsigned char buffer[16];

  uart_init(UART_BAUD_RATE);
  uart_send_str("Running AES test\r\n");

  // Setup AES config
  aes_cfg_t aes_cfg;
  aes_cfg.mode = AES_ENC;
  aes_cfg.key_len_in_bytes = 32;
  aes_cfg.manual_start_trigger = 0x0;
  aes_cfg.force_data_overwrite = 0x0;

  aes_key_put((const void *)key_32_1, aes_cfg.key_len_in_bytes);

  // Encode
  aes_cfg.mode = AES_ENC;
  aes_init(aes_cfg);
  aes_data_put_wait((const void *)plain_text_1);
  aes_data_get_wait((void *)buffer);

  // Check against golden cipher text
  for (int i = 0; i < 16; i++) {
    if (cipher_text_gold_32_1[i] != buffer[i]) {
      error++;
    }
  }

  // Decode
  aes_cfg.mode = AES_DEC;
  aes_init(aes_cfg);
  aes_data_put_wait((const void *)buffer);
  aes_data_get_wait((void *)buffer);

  // Check against input plain text
  for (int i = 0; i < 16; i++) {
    if (plain_text_1[i] != buffer[i]) {
      error++;
    }
  }

  if (error) {
    uart_send_str("FAIL!\r\n");
    while (1) {
    }
  } else {
    uart_send_str("PASS!\r\n");
    __asm__ volatile("wfi;");
  }

  return 0;
}
