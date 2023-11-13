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
   * Key length in words.
   */
  size_t key_len;
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
   * Plaintext and length (in bytes).
   */
  size_t plaintext_len;
  uint8_t *plaintext;
  /**
   * Authenticated data and length (in bytes).
   */
  size_t aad_len;
  uint8_t *aad;
  /**
   * Ciphertext (same length as plaintext).
   */
  uint8_t *ciphertext;
  /**
   * Authentication tag and length (in bytes). If the length is < 16 then the
   * last bytes are ignored.
   */
  size_t tag_len;
  uint8_t tag[16];
} aes_gcm_test_t;

/**
 * Call AES-GCM authenticated encryption for the given test vector.
 *
 * @param test The test vector to run
 * @param[out] cycles Cycle count for the encrypt() call
 * @return Test status
 */
status_t aes_gcm_testutils_encrypt(const aes_gcm_test_t *test,
                                   uint32_t *cycles);

/**
 * Call AES-GCM authenticated decryption for the given test vector.
 *
 * This function can be used to run negative tests on authentication, i.e. to
 * check that invalid tags fail. Simply set an invalid tag in the test vector
 * and check that `tag_valid` is false instead of true.
 *
 * @param test The test vector to run
 * @param[out] tag_valid True iff the tag passed its validity check
 * @param[out] cycles Cycle count for the decrypt() call
 * @return Test status
 */
status_t aes_gcm_testutils_decrypt(const aes_gcm_test_t *test,
                                   hardened_bool_t *tag_valid,
                                   uint32_t *cycles);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_AES_GCM_TESTUTILS_H_
