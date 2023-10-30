// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/aes_gcm_testutils.h"
#include "sw/device/tests/crypto/aes_gcm_testvectors.h"

// Global pointer to the current test vector.
const aes_gcm_test_t *current_test = NULL;

static status_t encrypt_test(void) {
  uint32_t cycles;
  TRY(aes_gcm_testutils_encrypt(current_test, &cycles));
  LOG_INFO("Encrypt cycles: %d", cycles);
  return OK_STATUS();
}

static status_t decrypt_test(void) {
  uint32_t cycles;
  hardened_bool_t tag_valid;
  TRY(aes_gcm_testutils_decrypt(current_test, &tag_valid, &cycles));
  LOG_INFO("Decrypt cycles: %d", cycles);
  TRY_CHECK(tag_valid == kHardenedBoolTrue);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  for (size_t i = 0; i < ARRAYSIZE(kAesGcmTestvectors); i++) {
    LOG_INFO("Starting AES-GCM test %d of %d...", i + 1,
             ARRAYSIZE(kAesGcmTestvectors));
    current_test = &kAesGcmTestvectors[i];
    LOG_INFO("Key length = %d", current_test->key_len * sizeof(uint32_t));
    LOG_INFO("Aad length = %d", current_test->aad_len);
    LOG_INFO("Encrypted data length = %d", current_test->plaintext_len);
    LOG_INFO("Tag length = %d", current_test->tag_len);
    EXECUTE_TEST(result, encrypt_test);
    EXECUTE_TEST(result, decrypt_test);
  }

  return status_ok(result);
}
