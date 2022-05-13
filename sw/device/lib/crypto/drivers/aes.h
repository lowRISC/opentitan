// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_AES_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /** Number of bits in an AES cipher block. */
  kAesBlockNumBits = 128,
  /** Number of bytes in an AES cipher block. */
  kAesBlockNumBytes = kAesBlockNumBits / 8,
  /** Number of words in an AES cipher block. */
  kAesBlockNumWords = kAesBlockNumBytes / sizeof(uint32_t),
};

/**
 * Error types for the AES driver.
 */
typedef enum aes_error {
  kAesOk = 0,
  /**
   * An internal error in the hardware which is not recoverable.
   *
   * If any function produces this value, all blocks produced in that
   * session must be discarded and the operation must be begun anew.
   */
  kAesInternalError = 1,
} aes_error_t;

/**
 * An AES block, which may represent plaintext or ciphertext.
 */
typedef struct aes_block {
  uint32_t data[kAesBlockNumWords];
} aes_block_t;

/**
 * A cipher mode supported natively by the AES hardware.
 */
typedef enum aes_cipher_mode {
  kAesCipherModeEcb,
  kAesCipherModeCbc,
  kAesCipherModeCfb,
  kAesCipherModeOfb,
  kAesCipherModeCtr,
} aes_cipher_mode_t;

/**
 * A key length supported by the AES hardware.
 */
typedef enum aes_key_len {
  kAesKeyLen128 = 128,
  kAesKeyLen192 = 192,
  kAesKeyLen256 = 256,
} aes_key_len_t;

/**
 * Parameters for initializing the AES hardware for performing a specific
 * encryption or decryption operation.
 */
typedef struct aes_params_t {
  /**
   * Whether to use the encryption or decryption operation.
   */
  bool encrypt;

  /**
   * The hardware-native cipher mode to apply, if any.
   */
  aes_cipher_mode_t mode;

  /**
   * The length of the key.
   */
  aes_key_len_t key_len;

  /**
   * The key, split into two shares. The actual key will be formed by
   * XORing both keys together.
   *
   * Neither entry may be null. If a non-shared key is desired, one of
   * the two pointers should be pointed to an array of zero-valued words
   * of sufficient length.
   */
  uint32_t *key[2];

  /**
   * The IV to use with the CBC or CTR modes.
   *
   * If the selected mode needs an IV, this pointer must not be null;
   * otherwise, its value is irrelevant.
   *
   * The IV must always be 128 bits.
   */
  uint32_t iv[4];
} aes_params_t;

/**
 * Prepares the AES hardware to perform an encryption or decryption operation,
 * which is described by the given parameters.
 *
 * @param params Parameters for the operation.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_begin(aes_params_t params);

/**
 * Advances the AES state by a single block.
 *
 * The AES hardware does not simply perform a single synchronous block
 * operation; there is a delay as a block makes it way through the hardware;
 * outputs are delayed one input from when it is fed into the hardware.
 *
 * Therefore, this function works thus:
 * 1. The contents of `src` are fed into the hardware (unless it is null, in
 *    which case this step is skipped).
 * 2. The contents of `dest` are filled with the hardware's output (again,
 *    unless it is null). `dest` may overlap with `src`.
 *
 * Operation of the driver will look something like this:
 * ```
 * aes_begin(...);
 * aes_update(NULL, input0);
 * aes_update(output0, input1);
 * // ...
 * aes_update(output(N-1), inputN);
 * aes_update(outputN, NULL);
 * aes_end();
 * ```
 *
 * @param dest The output block.
 * @param src The input block.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_update(aes_block_t *dest, const aes_block_t *src);

/**
 * Completes an AES session by clearing control settings and key material.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_end(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_AES_H_
