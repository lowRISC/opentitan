// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_AES_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
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
  kAesCipherModeEcb = 1,
  kAesCipherModeCbc = 2,
  kAesCipherModeCfb = 4,
  kAesCipherModeOfb = 8,
  kAesCipherModeCtr = 16,
} aes_cipher_mode_t;

/**
 * A key length supported by the AES hardware.
 *
 * The encoded values are used as identifiers to configure the hardware and
 * don't represent the key length in any specific format.
 */
typedef enum aes_key_len {
  kAesKeyLen128 = 1,
  kAesKeyLen192 = 2,
  kAesKeyLen256 = 4,
} aes_key_len_t;

/**
 * Represents an AES key.
 *
 * The key may be provided by software as two shares, or it may be a sideloaded
 * key that is produced by the keymgr and not visible to software.
 */
typedef struct aes_key {
  /**
   * Block cipher mode for which the key is intended.
   */
  aes_cipher_mode_t mode;

  /**
   * Whether the key is sideloaded.
   */
  hardened_bool_t sideload;

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
  const uint32_t *key_shares[2];
} aes_key_t;

/**
 * Prepares the AES hardware to perform an encryption operation.
 *
 * If `key.sideload` is true, then this routine does not load the key; the
 * caller must separately call keymgr to write the key into the AES block before
 * calling `aes_update`.
 *
 * If the selected mode requires an IV, then `iv` must not be null. Otherwise
 * (e.g. for ECB mode), `iv` is ignored and may be null.
 *
 * @param key Encryption key.
 * @param iv IV to use for non-ECB modes, 128 bits.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_encrypt_begin(const aes_key_t key, const aes_block_t *iv);

/**
 * Prepares the AES hardware to perform a decryption operation.
 *
 * If `key.sideload` is true, then this routine does not load the key; the
 * caller must separately call keymgr to write the key into the AES block before
 * calling `aes_update`.
 *
 * If the selected mode requires an IV, then `iv` must not be null. Otherwise
 * (e.g. for ECB mode), `iv` is ignored and may be null.
 *
 * @param key Encryption key.
 * @param iv IV to use for non-ECB modes, 128 bits.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_decrypt_begin(const aes_key_t key, const aes_block_t *iv);

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
 * aes_encrypt_begin(...);
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
