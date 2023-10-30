// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/aes_gcm/aes_gcm.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/aes_gcm_testutils.h"
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

  // Call AES-GCM decrypt with an incorrect tag (first word wrong).
  current_test->tag[0]++;
  uint32_t cycles_invalid1;
  hardened_bool_t valid;
  TRY(aes_gcm_testutils_decrypt(current_test, &valid, &cycles_invalid1));
  TRY_CHECK(valid == kHardenedBoolFalse);
  current_test->tag[0]--;
  LOG_INFO("First invalid tag: %d cycles", cycles_invalid1);

  // Call AES-GCM decrypt with an incorrect tag (middle word wrong).
  current_test->tag[tag_num_words / 2]++;
  uint32_t cycles_invalid2;
  TRY(aes_gcm_testutils_decrypt(current_test, &valid, &cycles_invalid2));
  TRY_CHECK(valid == kHardenedBoolFalse);
  current_test->tag[tag_num_words / 2]--;
  LOG_INFO("Second invalid tag: %d cycles", cycles_invalid2);

  // Call AES-GCM decrypt with an incorrect tag (last word wrong).
  current_test->tag[tag_num_words - 1]++;
  uint32_t cycles_invalid3;
  TRY(aes_gcm_testutils_decrypt(current_test, &valid, &cycles_invalid3));
  TRY_CHECK(valid == kHardenedBoolFalse);
  current_test->tag[tag_num_words - 1]--;
  LOG_INFO("Third invalid tag: %d cycles", cycles_invalid3);

  // Check that the cycle counts for the invalid tags match.
  TRY_CHECK(
      cycles_invalid1 == cycles_invalid2,
      "AES-GCM decryption was not constant-time for different invalid tags");
  TRY_CHECK(
      cycles_invalid2 == cycles_invalid3,
      "AES-GCM decryption was not constant-time for different invalid tags");
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  status_t result;
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
