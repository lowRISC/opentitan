// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define ENTROPY_SRC_CONF_REG_OFFSET 0x18
#define CSRNG_CTRL_REG_OFFSET 0x14
#define EDN_CTRL_REG_OFFSET 0x14

// The following plaintext, key and ciphertext are extracted from Appendix C of
// the Advanced Encryption Standard (AES) FIPS Publication 197 available at
// https://www.nist.gov/publications/advanced-encryption-standard-aes

#define KEY_LENGTH_IN_BYTES 32
#define TEXT_LENGTH_IN_BYTES 16
#define TEXT_LENGTH_IN_WORDS (TEXT_LENGTH_IN_BYTES / 4)

static const uint8_t kPlainText[TEXT_LENGTH_IN_BYTES] = {
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
    0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
};

static const uint8_t kKey[KEY_LENGTH_IN_BYTES] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
    0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
};

static const uint8_t kCipherTextGold[TEXT_LENGTH_IN_BYTES] = {
    0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf,
    0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89,
};

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.
static const uint8_t kKeyShare1[KEY_LENGTH_IN_BYTES] = {
    0x0f, 0x1f, 0x2f, 0x3F, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};

const test_config_t kTestConfig;

static bool aes_input_ready(const dif_aes_t *aes) {
  bool status;
  CHECK(dif_aes_get_status(aes, kDifAesStatusInputReady, &status) == kDifAesOk);

  return status;
}

static bool aes_output_valid(const dif_aes_t *aes) {
  bool status;
  CHECK(dif_aes_get_status(aes, kDifAesStatusOutputValid, &status) ==
        kDifAesOk);

  return status;
}

bool test_main(void) {
  dif_aes_t aes;

  LOG_INFO("Running AES test");

  // First of all, we need to get the entropy complex up and running.
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR),
                      ENTROPY_SRC_CONF_REG_OFFSET, 0x2);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                      CSRNG_CTRL_REG_OFFSET, 0x1);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, 0x1);

  // Initialise AES.
  dif_aes_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR),
  };
  CHECK(dif_aes_init(params, &aes) == kDifAesOk);
  CHECK(dif_aes_reset(&aes) == kDifAesResetOk);

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[KEY_LENGTH_IN_BYTES];
  for (int i = 0; i < KEY_LENGTH_IN_BYTES; ++i) {
    key_share0[i] = kKey[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(&key.share0[0], &key_share0[0], KEY_LENGTH_IN_BYTES);
  memcpy(&key.share1[0], &kKeyShare1[0], KEY_LENGTH_IN_BYTES);

  // Setup ECB encryption transaction.
  dif_aes_transaction_t transaction = {
      .key_len = kDifAesKey256,
      .mode = kDifAesModeEncrypt,
      .operation = kDifAesOperationAuto,
  };
  CHECK(dif_aes_start_ecb(&aes, &transaction, key) == kDifAesStartOk);

  // "Convert" plain data byte arrays to `dif_aes_data_t`.
  dif_aes_data_t in_data_plain;
  memcpy(&in_data_plain.data[0], &kPlainText[0], TEXT_LENGTH_IN_BYTES);

  // Load the plain text to trigger the encryption operation.
  while (!aes_input_ready(&aes)) {
  }
  CHECK(dif_aes_load_data(&aes, in_data_plain) == kDifAesLoadDataOk);

  // Read out the produced cipher text.
  dif_aes_data_t out_data_cipher;
  while (!aes_output_valid(&aes)) {
  }
  CHECK(dif_aes_read_output(&aes, &out_data_cipher) == kDifAesReadOutputOk);

  // Finish the ECB encryption transaction.
  CHECK(dif_aes_end(&aes) == kDifAesEndOk);

  // Check the produced cipher text against the reference.
  uint32_t cipher_text_gold_words[TEXT_LENGTH_IN_WORDS];
  memcpy(&cipher_text_gold_words[0], &kCipherTextGold[0], TEXT_LENGTH_IN_BYTES);
  for (int i = 0; i < TEXT_LENGTH_IN_WORDS; ++i) {
    CHECK(cipher_text_gold_words[i] == out_data_cipher.data[i],
          "Encrypted cipher text mismatched: exp = %x, actual = %x",
          cipher_text_gold_words[i], out_data_cipher.data[i]);
  }

  // Disable and re-enable EDN0 to get some more entropy out of it. This is
  // dirty and needs to be reworked. We need to setup CSRNG/EDN to continously
  // provide entropy.
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, 0x0);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, 0x1);

  // Setup ECB decryption transaction.
  transaction.mode = kDifAesModeDecrypt;
  CHECK(dif_aes_start_ecb(&aes, &transaction, key) == kDifAesStartOk);

  // Load the previously produced cipher text to start the decryption operation.
  while (!aes_input_ready(&aes)) {
  }
  CHECK(dif_aes_load_data(&aes, out_data_cipher) == kDifAesLoadDataOk);

  // Read out the produced plain text.

  dif_aes_data_t out_data_plain;
  while (!aes_output_valid(&aes)) {
  }
  CHECK(dif_aes_read_output(&aes, &out_data_plain) == kDifAesReadOutputOk);

  // Finish the ECB encryption transaction.
  CHECK(dif_aes_end(&aes) == kDifAesEndOk);

  // Check the produced plain text against the reference.
  uint32_t plain_text_gold_words[TEXT_LENGTH_IN_WORDS];
  memcpy(&plain_text_gold_words[0], &kPlainText[0], TEXT_LENGTH_IN_BYTES);
  for (int i = 0; i < TEXT_LENGTH_IN_WORDS; ++i) {
    CHECK(plain_text_gold_words[i] == out_data_plain.data[i],
          "Decrypted text mismatched: exp = %x, actual = %x",
          plain_text_gold_words[i], out_data_plain.data[i]);
  }

  return true;
}
