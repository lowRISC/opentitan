// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"

#include "sw/device/lib/base/log.h"
#include "sw/device/lib/runtime/check.h"
#include "sw/device/lib/testing/test_main.h"

// The following plaintext, key and ciphertext are extracted from Appendix C of
// the Advanced Encryption Standard (AES) FIPS Publication 197 available at
// https://www.nist.gov/publications/advanced-encryption-standard-aes

static const uint8_t plain_text_1[16] = {0x00, 0x11, 0x22, 0x33, 0x44, 0x55,
                                         0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
                                         0xcc, 0xdd, 0xee, 0xff};

static const uint8_t key_32_1[32] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
    0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f};

static const uint8_t cipher_text_gold_32_1[16] = {
    0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf,
    0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89};

bool test_main(void) {
  // Wait for AES unit being idle
  while (!aes_idle()) {
  }

  uint8_t buffer[16];

  LOG_INFO("Running AES test");

  // Setup AES config
  aes_cfg_t aes_cfg = {
      .mode = kAesEcb, .key_len = kAes256, .manual_operation = false,
  };

  aes_key_put(key_32_1, aes_cfg.key_len);

  // Encode
  aes_cfg.operation = kAesEnc;
  aes_init(aes_cfg);
  aes_data_put_wait(plain_text_1);
  aes_data_get_wait(buffer);

  // Check against golden cipher text
  for (int i = 0; i < 16; i++) {
    CHECK(cipher_text_gold_32_1[i] == buffer[i],
          "Encoded cipher_text[%d] mismatched: exp = %x, actual = %x", i,
          cipher_text_gold_32_1[i], buffer[i]);
  }

  // Decode
  aes_cfg.operation = kAesDec;
  aes_init(aes_cfg);
  aes_data_put_wait(buffer);
  aes_data_get_wait(buffer);

  // Check against input plain text
  for (int i = 0; i < 16; i++) {
    CHECK(plain_text_1[i] == buffer[i],
          "Decoded plain_text[%d] mismatched: exp = %x, actual = %x", i,
          plain_text_1[i], buffer[i]);
  }

  // Clear
  aes_clear();

  return true;
}
