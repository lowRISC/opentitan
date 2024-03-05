// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_SIGVERIFY_ECDSA_P256_KEY_H_
#define OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_SIGVERIFY_ECDSA_P256_KEY_H_

#include <stdint.h>

#include "sw/lib/sw/device/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /** Number of 32-bit words in a P-256 public key. */
  kP256PublicKeyWords = 512 / 32,
};

/**
 * A type that holds `kP256PublicKeyWords` words.
 *
 * This can be used to store ECDSA P256 public keys or signatures.
 */
typedef struct sigverify_ecdsa_p256_buffer {
  uint32_t data[kP256PublicKeyWords];
} sigverify_ecdsa_p256_buffer_t;

/**
 * Gets the ID of an ECDSA public key.
 *
 * ID of a key is the least significant word of its key buffer.
 * Callers must make sure that `pub_key` is valid before calling this function.
 *
 * @param key An ECDSA P256 public key.
 * @return ID of the key.
 */
OT_WARN_UNUSED_RESULT
inline uint32_t sigverify_ecdsa_key_id_get(
    const sigverify_ecdsa_p256_buffer_t *pub_key) {
  return pub_key->data[0];
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_SIGVERIFY_ECDSA_P256_KEY_H_
