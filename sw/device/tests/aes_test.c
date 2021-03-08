// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define ENTROPY_SRC_CONF_REG_OFFSET 0x18
#define CSRNG_CTRL_REG_OFFSET 0x14
#define EDN_CTRL_REG_OFFSET 0x14

// TODO:
// 1) Use the dif_aes directly.

// The following plaintext, key and ciphertext are extracted from Appendix C of
// the Advanced Encryption Standard (AES) FIPS Publication 197 available at
// https://www.nist.gov/publications/advanced-encryption-standard-aes

static const uint8_t kPlainText[16] = {0x00, 0x11, 0x22, 0x33, 0x44, 0x55,
                                       0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
                                       0xcc, 0xdd, 0xee, 0xff};

static const uint8_t kKey[32] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
    0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f};

static const uint8_t kCipherTextGold[16] = {0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67,
                                            0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90,
                                            0x4b, 0x49, 0x60, 0x89};

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.
static const uint8_t kKeyShare1[32] = {
    0x0f, 0x1f, 0x2f, 0x3F, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa};

const test_config_t kTestConfig;

bool test_main(void) {
  // First of all, we need to get the entropy complex up and running.
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR),
                      ENTROPY_SRC_CONF_REG_OFFSET, 0x2);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                      CSRNG_CTRL_REG_OFFSET, 0x1);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, 0x1);

  // Wait for AES unit being idle
  while (!aes_idle()) {
  }

  uint8_t buffer[16];

  LOG_INFO("Running AES test");

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[32];
  for (int i = 0; i < 32; ++i) {
    key_share0[i] = kKey[i] ^ kKeyShare1[i];
  }

  // Setup AES config
  aes_cfg_t aes_cfg = {
      .mode = kAesEcb,
      .key_len = kAes256,
      .manual_operation = false,
  };

  // Encode
  aes_cfg.operation = kAesEnc;
  aes_init(aes_cfg);
  aes_key_put(key_share0, kKeyShare1, aes_cfg.key_len);
  aes_data_put_wait(kPlainText);
  aes_data_get_wait(buffer);

  // Check against golden cipher text
  for (int i = 0; i < 16; ++i) {
    CHECK(kCipherTextGold[i] == buffer[i],
          "Encrypted cipher_text[%d] mismatched: exp = %x, actual = %x", i,
          kCipherTextGold[i], buffer[i]);
  }

  // Disable and re-enable EDN0 to get some more entropy out of it. This is
  // dirty and needs to be reworked. We need to setup CSRNG/EDN to continously
  // provide entropy.
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, 0x0);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, 0x1);

  // Decode
  aes_cfg.operation = kAesDec;
  aes_init(aes_cfg);
  aes_key_put(key_share0, kKeyShare1, aes_cfg.key_len);
  aes_data_put_wait(buffer);
  aes_data_get_wait(buffer);

  // Check against input plain text
  for (int i = 0; i < 16; ++i) {
    CHECK(kPlainText[i] == buffer[i],
          "Decrypted plain_text[%d] mismatched: exp = %x, actual = %x", i,
          kPlainText[i], buffer[i]);
  }

  // Clear
  aes_clear();

  return true;
}
