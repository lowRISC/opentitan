// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/aes_gcm_testutils.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/impl/aes_gcm/aes_gcm.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

/**
 * Start a cycle-count timing profile.
 */
static uint64_t profile_start() { return ibex_mcycle_read(); }

/**
 * End a cycle-count timing profile.
 *
 * Call `profile_start()` first.
 */
static uint32_t profile_end(uint64_t t_start) {
  uint64_t t_end = ibex_mcycle_read();
  uint64_t cycles = t_end - t_start;
  CHECK(cycles <= UINT32_MAX);
  return (uint32_t)cycles;
}

uint32_t call_aes_gcm_encrypt(aes_gcm_test_t test) {
  uint8_t actual_ciphertext[test.plaintext_len];
  uint8_t actual_tag[kAesGcmTagNumBytes];

  // Construct AES key. Construct key shares by setting first share to full key
  // and second share to 0. (Note: this is not a secure construction! But it
  // makes debugging tests easier because there is only one thing to print.)
  const uint32_t share1[8] = {0};
  const aes_key_t test_key = {
      .mode = kAesCipherModeCtr,
      .sideload = kHardenedBoolFalse,
      .key_len = test.key_len,
      .key_shares = {test.key, share1},
  };

  // Call encrypt() with a cycle count timing profile.
  uint64_t t_start = profile_start();
  aes_error_t err = aes_gcm_encrypt(
      test_key, test.iv_len, test.iv, test.plaintext_len, test.plaintext,
      test.aad_len, test.aad, actual_ciphertext, actual_tag);
  uint32_t cycles = profile_end(t_start);
  LOG_INFO("aes_gcm_encrypt took %d cycles", cycles);

  // Check for errors and that the tag and plaintext match expected values.
  CHECK(err == kAesOk, "AES-GCM encryption returned an error: %08x", err);
  CHECK_ARRAYS_EQ(actual_tag, test.tag, sizeof(test.tag));
  if (test.plaintext_len > 0) {
    int cmp = memcmp(actual_ciphertext, test.ciphertext, test.plaintext_len);
    CHECK(cmp == 0, "AES-GCM encryption output does not match ciphertext");
  }

  return cycles;
}

uint32_t call_aes_gcm_decrypt(aes_gcm_test_t test, bool tag_valid) {
  hardened_bool_t success;
  uint8_t actual_plaintext[test.plaintext_len];

  // Construct AES key. Construct key shares by setting first share to full key
  // and second share to 0. (Note: this is not a secure construction! But it
  // makes debugging tests easier because there is only one thing to print.)
  const uint32_t share1[8] = {0};
  const aes_key_t test_key = {
      .mode = kAesCipherModeCtr,
      .sideload = kHardenedBoolFalse,
      .key_len = test.key_len,
      .key_shares = {test.key, share1},
  };

  // Call decrypt() with a cycle count timing profile.
  uint64_t t_start = profile_start();
  aes_error_t err = aes_gcm_decrypt(
      test_key, test.iv_len, test.iv, test.plaintext_len, test.ciphertext,
      test.aad_len, test.aad, test.tag, actual_plaintext, &success);
  uint32_t cycles = profile_end(t_start);
  LOG_INFO("aes_gcm_decrypt took %d cycles", cycles);

  // Check the results.
  CHECK(err == kAesOk, "AES-GCM decryption returned an error: %08x", err);
  if (tag_valid) {
    CHECK(success == kHardenedBoolTrue,
          "AES-GCM decryption failed on valid input");
    if (test.plaintext_len > 0) {
      int cmp = memcmp(actual_plaintext, test.plaintext, test.plaintext_len);
      CHECK(cmp == 0, "AES-GCM decryption output does not match plaintext");
    }
  } else {
    CHECK(success == kHardenedBoolFalse,
          "AES-GCM decryption passed an invalid tag");
  }

  return cycles;
}
