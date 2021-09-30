// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/tests/aes_example_values.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

static bool aes_input_ready(const dif_aes_t *aes) {
  bool status;
  CHECK_DIF_OK(dif_aes_get_status(aes, kDifAesStatusInputReady, &status));

  return status;
}

static bool aes_output_valid(const dif_aes_t *aes) {
  bool status;
  CHECK_DIF_OK(dif_aes_get_status(aes, kDifAesStatusOutputValid, &status));

  return status;
}

bool test_main(void) {
  dif_aes_t aes;

  LOG_INFO("Running AES test");

  // First of all, we need to get the entropy complex up and running.
  entropy_testutils_boot_mode_init();

  // Initialise AES.
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

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
  CHECK_DIF_OK(dif_aes_start_ecb(&aes, &transaction, key));

  // "Convert" plain data byte arrays to `dif_aes_data_t`.
  dif_aes_data_t in_data_plain;
  memcpy(&in_data_plain.data[0], &kPlainText[0], TEXT_LENGTH_IN_BYTES);

  // Load the plain text to trigger the encryption operation.
  while (!aes_input_ready(&aes)) {
  }
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Read out the produced cipher text.
  dif_aes_data_t out_data_cipher;
  while (!aes_output_valid(&aes)) {
  }
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data_cipher));

  // Finish the ECB encryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));

  // Check the produced cipher text against the reference.
  uint32_t cipher_text_gold_words[TEXT_LENGTH_IN_WORDS];
  memcpy(&cipher_text_gold_words[0], &kCipherTextGold[0], TEXT_LENGTH_IN_BYTES);
  for (int i = 0; i < TEXT_LENGTH_IN_WORDS; ++i) {
    CHECK(cipher_text_gold_words[i] == out_data_cipher.data[i],
          "Encrypted cipher text mismatched: exp = %x, actual = %x",
          cipher_text_gold_words[i], out_data_cipher.data[i]);
  }

  // Setup ECB decryption transaction.
  transaction.mode = kDifAesModeDecrypt;
  CHECK_DIF_OK(dif_aes_start_ecb(&aes, &transaction, key));

  // Load the previously produced cipher text to start the decryption operation.
  while (!aes_input_ready(&aes)) {
  }
  CHECK_DIF_OK(dif_aes_load_data(&aes, out_data_cipher));

  // Read out the produced plain text.

  dif_aes_data_t out_data_plain;
  while (!aes_output_valid(&aes)) {
  }
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data_plain));

  // Finish the ECB encryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));

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
