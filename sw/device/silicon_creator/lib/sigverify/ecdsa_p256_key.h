// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_ECDSA_P256_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_ECDSA_P256_KEY_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of a coordinate for an attestation public key in bits.
   */
  kEcdsaP256PublicKeyCoordBits = 256,
  /**
   * Size of a coordinate for an attestation public key in bytes.
   */
  kEcdsaP256PublicKeyCoordBytes = kEcdsaP256PublicKeyCoordBits / 8,
  /**
   * Size of a coordinate for an attestation public key in 32b words.
   */
  kEcdsaP256PublicKeyCoordWords =
      kEcdsaP256PublicKeyCoordBytes / sizeof(uint32_t),
  /**
   * Size of an attestation signature component in bits.
   */
  kEcdsaP256SignatureComponentBits = 256,
  /**
   * Size of an attestation signature component in bytes.
   */
  kEcdsaP256SignatureComponentBytes = kEcdsaP256SignatureComponentBits / 8,
  /**
   * Size of an attestation signature component in 32b words.
   */
  kEcdsaP256SignatureComponentWords =
      kEcdsaP256SignatureComponentBytes / sizeof(uint32_t),
  /**
   * Size of an attestation signature in bits.
   */
  kAttestationSignatureBits = kEcdsaP256SignatureComponentBits * 2,
  /**
   * Size of an attestation signature in bytes.
   */
  kAttestationSignatureBytes = kAttestationSignatureBits / 8,
  /**
   * Size of an attestation signature in 32b words.
   */
  kAttestationSignatureWords = kAttestationSignatureBytes / sizeof(uint32_t),
};

/**
 * Holds an attestation public key (ECDSA-P256).
 */
typedef struct ecdsa_p256_public_key {
  /**
   * Affine x-coordinate of the point.
   */
  uint32_t x[kEcdsaP256PublicKeyCoordWords];
  /**
   * Affine y-coordinate of the point.
   */
  uint32_t y[kEcdsaP256PublicKeyCoordWords];
} ecdsa_p256_public_key_t;

/**
 * Holds an attestation signature (ECDSA-P256).
 */
typedef struct ecdsa_p256_signature {
  uint32_t r[kEcdsaP256SignatureComponentWords];
  uint32_t s[kEcdsaP256SignatureComponentWords];
} ecdsa_p256_signature_t;

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
inline uint32_t sigverify_ecdsa_p256_key_id_get(
    const ecdsa_p256_public_key_t *pub_key) {
  return pub_key->x[0];
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_ECDSA_P256_KEY_H_
