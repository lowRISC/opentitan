// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/aes_gcm_testutils.h"
#include "sw/device/tests/crypto/aes_gcm_testvectors.h"

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  for (size_t i = 0; i < ARRAYSIZE(kAesGcmTestvectors); i++) {
    LOG_INFO("Starting AES-GCM test %d of %d...", i + 1,
             ARRAYSIZE(kAesGcmTestvectors));
    const aes_gcm_test_t test = kAesGcmTestvectors[i];

    // Call AES-GCM encrypt.
    uint32_t encrypt_cycles = call_aes_gcm_encrypt(test);

    // Call AES-GCM decrypt.
    uint32_t decrypt_cycles = call_aes_gcm_decrypt(test, /*tag_valid=*/true);

    LOG_INFO("Encrypt cycles: %d", encrypt_cycles);
    LOG_INFO("Decrypt cycles: %d", decrypt_cycles);
    LOG_INFO("Finished AES-GCM test %d.", i + 1);
  }

  return true;
}
