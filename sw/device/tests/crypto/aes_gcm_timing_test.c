// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/aes_gcm/aes_gcm.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/aes_gcm_testutils.h"
#include "sw/device/tests/crypto/aes_gcm_testvectors.h"

/**
 * Checks that decryption takes the same number of cycles regardless of tag.
 *
 * This test ensures that the AES-GCM tag check takes the exact same amount of
 * time for all *incorrect* tags; if it didn't, for instance exiting early at
 * the first incorrect byte, then an attacker could guess one byte at a time
 * and observe the timing to see if the byte was correct.
 *
 * It's OK if decryption takes a different amount of time with a correct tag
 * than with an incorrect one.
 *
 * @param test Test vector to use
 */
static void test_decrypt_timing(aes_gcm_test_t test) {
  // Call AES-GCM decrypt with an incorrect tag (first word wrong).
  test.tag[0]++;
  uint32_t cycles_invalid1 = call_aes_gcm_decrypt(test, /*tag_valid=*/false);
  test.tag[0]--;

  // Call AES-GCM decrypt with an incorrect tag (middle word wrong).
  test.tag[kAesGcmTagNumWords / 2]++;
  uint32_t cycles_invalid2 = call_aes_gcm_decrypt(test, /*tag_valid=*/false);
  test.tag[kAesGcmTagNumWords / 2]--;

  // Call AES-GCM decrypt with an incorrect tag (last word wrong).
  test.tag[kAesGcmTagNumWords - 1]++;
  uint32_t cycles_invalid3 = call_aes_gcm_decrypt(test, /*tag_valid=*/false);
  test.tag[kAesGcmTagNumWords - 1]--;

  // Check that the cycle counts for the invalid tags match.
  CHECK(cycles_invalid1 == cycles_invalid2,
        "AES-GCM decryption was not constant-time for different invalid tags");
  CHECK(cycles_invalid2 == cycles_invalid3,
        "AES-GCM decryption was not constant-time for different invalid tags");
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  for (size_t i = 0; i < ARRAYSIZE(kAesGcmTestvectors); i++) {
    LOG_INFO("Starting AES-GCM timing test %d of %d...", i + 1,
             ARRAYSIZE(kAesGcmTestvectors));

    test_decrypt_timing(kAesGcmTestvectors[i]);

    LOG_INFO("Finished AES-GCM timing test %d.", i + 1);
  }

  return true;
}
