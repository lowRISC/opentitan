// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/check.h"
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

// CLKMGR CFG and Definitions

void test_aes_hint_set(const dif_clkmgr_t *clkmgr) {
  // Write the AES clk hint to 1 within clkmgr to indicate AES clk is ready to be gated.
  //  Verify that the AES clk hint status within clkmgr reads 0 (AES is idle).p
  //
  // Get the initial state of the hint for the clock The clock hint might be
  // enabled or disabled depending on reset behavior - either is fine for the
  // purposes of this test.
  //
  // to allow the clock to be gated we disable the hint which the test plan
  // suggests writes a 1
  bool enabled;
  CHECK(dif_clkmgr_hintable_clock_get_hint(clkmgr, kTopEarlgreyHintableClocksMainAes, &enabled) ==
        kDifClkmgrOk);

  bool expected = false;
  CHECK(dif_clkmgr_hintable_clock_set_hint(
            clkmgr, kTopEarlgreyHintableClocksMainAes,
            expected ? kDifClkmgrToggleEnabled
                     : kDifClkmgrToggleDisabled) == kDifClkmgrOk);
  CHECK(dif_clkmgr_hintable_clock_get_hint(clkmgr, kTopEarlgreyHintableClocksMainAes, &enabled) ==
        kDifClkmgrOk);
  CHECK(enabled == expected);
}

void test_aes_hint_active(const dif_clkmgr_t *clkmgr) {
  // Verify that the AES clk hint status within clkmgr now reads 1 (AES is not idle),
  //   before the AES operation is complete.
  bool enabled;
  CHECK(dif_clkmgr_hintable_clock_get_hint(clkmgr, kTopEarlgreyHintableClocksMainAes, &enabled) ==
        kDifClkmgrOk);
  CHECK(enabled == true);
}

void test_aes_hint_idle(const dif_clkmgr_t *clkmgr) {
  // Verify that the AES clk hint status within clkmgr now reads 0 again (AES is idle),
  //   after the AES operation is complete.
  bool enabled;
  CHECK(dif_clkmgr_hintable_clock_get_hint(clkmgr, kTopEarlgreyHintableClocksMainAes, &enabled) ==
        kDifClkmgrOk);
  CHECK(enabled == false);
}


/**
 * Test that AES 'hintable' clock, indirectly controlled by software,
 * can have its hint toggled and status checked.
 */
void test_aes_clock(const dif_clkmgr_t *clkmgr) {

  // Get the initial state of the hint for the clock The clock hint might be
  // enabled or disabled depending on reset behavior - either is fine for the
  // purposes of this test.
  bool enabled;
  CHECK(dif_clkmgr_hintable_clock_get_hint(clkmgr, kTopEarlgreyHintableClocksMainAes, &enabled) ==
        kDifClkmgrOk);

  // Toggle the hint twice so that it ends up in its original state.
  for (int j = 0; j < 2; ++j) {
    bool expected = !enabled;
    CHECK(dif_clkmgr_hintable_clock_set_hint(
              clkmgr, kTopEarlgreyHintableClocksMainAes,
              expected ? kDifClkmgrToggleEnabled
                       : kDifClkmgrToggleDisabled) == kDifClkmgrOk);
    CHECK(dif_clkmgr_hintable_clock_get_hint(clkmgr, kTopEarlgreyHintableClocksMainAes, &enabled) ==
          kDifClkmgrOk);
    CHECK(enabled == expected);

    // If the clock hint is enabled then the clock should always be enabled.
    if (enabled) {
      bool status = false;
      CHECK(dif_clkmgr_hintable_clock_get_enabled(clkmgr, kTopEarlgreyHintableClocksMainAes, &status) ==
            kDifClkmgrOk);
      CHECK(status, "clock %u hint is enabled but status is disabled", kTopEarlgreyHintableClocksMainAes);
    }
  }
}


bool test_main(void) {
  const dif_clkmgr_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR),
      .last_gateable_clock = kTopEarlgreyGateableClocksLast,
      .last_hintable_clock = kTopEarlgreyHintableClocksLast,
  };

  dif_aes_t aes;
  dif_clkmgr_t clkmgr;

  CHECK(dif_clkmgr_init(params, &clkmgr) == kDifClkmgrOk);

  LOG_INFO("Entropy complex ini...");
  // First of all, we need to get the entropy complex up and running.
  entropy_testutils_boot_mode_init();

  LOG_INFO("AES ini...");
  // Initialise AES.
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  LOG_INFO("Set AES hint");
  test_aes_hint_set(&clkmgr);

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[KEY_LENGTH_IN_BYTES];
  for (int i = 0; i < KEY_LENGTH_IN_BYTES; ++i) {
    key_share0[i] = kKey[i] ^ kKeyShare1[i];
  }

  LOG_INFO("copy keyshare to AES...");
  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(&key.share0[0], &key_share0[0], KEY_LENGTH_IN_BYTES);
  memcpy(&key.share1[0], &kKeyShare1[0], KEY_LENGTH_IN_BYTES);

  LOG_INFO("triggeringECB encryption...");
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


  LOG_INFO("polling for aes input ready...");
  // Load the plain text to trigger the encryption operation.
  while (!aes_input_ready(&aes)) {
  }
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  //Verify that the AES clk hint status within clkmgr now reads 1 (AES is not
  //idle), before the AES operation is complete.
  test_aes_hint_active(&clkmgr);

  // Read out the produced cipher text.
  dif_aes_data_t out_data_cipher;

  LOG_INFO("polling for aes output...");
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

  //Verify that the AES clk hint status within clkmgr now reads 0 again (AES is
  //idle), after the AES operation is complete.
  test_aes_hint_idle(&clkmgr);

  return true;
}
