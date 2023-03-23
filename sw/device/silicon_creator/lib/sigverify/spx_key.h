// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_KEY_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Length of an SPX public key in bits.
   */
  kSigverifySpxKeyNumBits = 256,
  /**
   * Length of an SPX public key in bytes.
   */
  kSigVerifySpxKeyBytes = kSigverifySpxKeyNumBits / 8,
  /**
   * Length of an SPX public key in words.
   */
  kSigVerifySpxKeyWords = kSigVerifySpxKeyBytes / sizeof(uint32_t),
};

/**
 * An SPX public key.
 */
typedef struct sigverify_spx_key {
  /**
   * A `kSigVerifySpxNumWords` base 2^32 digit integer, little-endian.
   */
  uint32_t data[kSigVerifySpxKeyWords];
} sigverify_spx_key_t;

/**
 * Gets the ID of an SPX public key.
 *
 * ID of a key is its least significant word.
 * Callers must make sure that `key` is valid before calling this function.
 *
 * @param key An SPX public key.
 * @return ID of the key.
 */
inline uint32_t sigverify_spx_key_id_get(const sigverify_spx_key_t *key) {
  return key->data[0];
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_KEY_H_
