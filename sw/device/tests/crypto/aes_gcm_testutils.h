// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_AES_GCM_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_AES_GCM_TESTUTILS_H_

#include <stdbool.h>

#include "sw/device/lib/crypto/drivers/aes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef struct aes_gcm_test {
  /**
   * Key length.
   */
  aes_key_len_t key_len;
  /**
   * Key material (length = key_len).
   */
  const uint32_t *key;
  /**
   * IV and length (in bytes). If IV length is < 16 then the last bytes are
   * ignored.
   */
  size_t iv_len;
  uint8_t iv[16];
  /**
   * Plaintext and length (in bytes). If the length is not a multiple of 4,
   * then the most significant bytes of the last word are ignored.
   */
  size_t plaintext_len;
  uint8_t *plaintext;
  /**
   * Authenticated data and length (in bytes). If the length is not a multiple
   * of 4, then the most significant bytes of the last word are ignored.
   */
  size_t aad_len;
  uint8_t *aad;
  /**
   * Authentication tag.
   */
  uint8_t tag[16];
  /**
   * Ciphertext (same length as plaintext).
   */
  uint8_t *ciphertext;
} aes_gcm_test_t;

/**
 * Call AES-GCM authenticated encryption for the given test vector.
 *
 * @param test The test vector to run
 * @return Cycle count for the encrypt() call
 */
uint32_t call_aes_gcm_encrypt(aes_gcm_test_t test);

/**
 * Call AES-GCM authenticated decryption for the given test vector.
 *
 * @param test The test vector to run
 * @param plaintext Buffer for the output plaintext
 * @param tag_valid True iff the tag is expected to be valid
 * @return Cycle count for the decrypt() call
 */
uint32_t call_aes_gcm_decrypt(aes_gcm_test_t test, bool tag_valid);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_AES_GCM_TESTUTILS_H_
