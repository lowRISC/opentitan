// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/aes_gcm/aes_gcm.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/aes_gcm_testvectors.h"

// Global pointer to the current test vector.
static aes_gcm_test_t *current_test = NULL;

/**
 * Checks that decryption takes the same number of cycles regardless of tag.
 *
 * This test ensures that the AES-GCM tag check takes the exact same amount of
 * time for all *incorrect* tags; if it didn't, for instance exiting early at
 * the first incorrect byte, then an attacker could guess one byte at a time
 * and observe the timing to see if the byte was correct.
 *
 * Invalidates icache before each test so that each starts from the same state.
 *
 * It's OK if decryption takes a different amount of time with a correct tag
 * than with an incorrect one.
 */
static status_t test_decrypt_timing(void) {
  size_t tag_num_words = current_test->tag_len / sizeof(uint32_t);
  TRY_CHECK(tag_num_words * sizeof(uint32_t) == current_test->tag_len,
            "Tag length %d is not a multiple of the word size (%d).",
            current_test->tag_len, sizeof(uint32_t));

  // Construct the internal AES key representation.
  uint32_t dummy_share[8] = {0};
  aes_key_t aes_key = {
      .mode = kAesCipherModeCtr,
      .key_len = current_test->key_len,
      .key_shares = {(uint32_t *)current_test->key, dummy_share},
      .sideload = kHardenedBoolFalse,
  };
  aes_key.checksum = aes_key_integrity_checksum(&aes_key);

  // Initialize the internal base context.
  aes_gcm_context_t base_ctx;
  size_t iv_num_words = current_test->iv_len / sizeof(uint32_t);

  TRY(aes_gcm_decrypt_init(aes_key, iv_num_words, (uint32_t *)current_test->iv,
                           &base_ctx));

  aes_gcm_context_t test_ctx;
  size_t output_len;
  uint8_t dummy_output[16];
  hardened_bool_t valid;
  uint32_t cycles[3];

  // We test the first word, the middle word, and the last word.
  size_t wrong_word_indices[3] = {0, tag_num_words / 2, tag_num_words - 1};

  // Run in a loop to guarantee the same behaviour each time.
  for (size_t i = 0; i < 3; i++) {
    size_t idx = wrong_word_indices[i];
    memcpy(&test_ctx, &base_ctx, sizeof(aes_gcm_context_t));

    current_test->tag[idx]++;

    uint64_t t_start = profile_start();
    aes_gcm_decrypt_final(&test_ctx, tag_num_words,
                          (uint32_t *)current_test->tag, &output_len,
                          dummy_output, &valid);
    cycles[i] = profile_end(t_start);

    TRY_CHECK(valid == kHardenedBoolFalse);
    current_test->tag[idx]--;
    LOG_INFO("Invalid tag at word %d: %d cycles", idx, cycles[i]);
  }

  // Check that the cycle counts for the invalid tags match exactly.
  TRY_CHECK(
      cycles[0] == cycles[1],
      "AES-GCM decryption was not constant-time for different invalid tags");
  TRY_CHECK(
      cycles[1] == cycles[2],
      "AES-GCM decryption was not constant-time for different invalid tags");
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  status_t result = OK_STATUS();
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));
  hardened_bool_t icache_enabled;
  CHECK_STATUS_OK(otcrypto_disable_icache(&icache_enabled));
  for (size_t i = 0; i < ARRAYSIZE(kAesGcmTestvectors); i++) {
    current_test = &kAesGcmTestvectors[i];
    LOG_INFO("Key length = %d", current_test->key_len * sizeof(uint32_t));
    LOG_INFO("Aad length = %d", current_test->aad_len);
    LOG_INFO("Encrypted data length = %d", current_test->plaintext_len);
    LOG_INFO("Tag length = %d", current_test->tag_len);
    EXECUTE_TEST(result, test_decrypt_timing);
  }

  return status_ok(result);
}
