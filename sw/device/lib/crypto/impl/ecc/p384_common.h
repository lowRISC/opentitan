// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_COMMON_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_COMMON_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Length of a P-384 curve point coordinate in bits (modulo p).
   */
  kP384CoordBits = 384,
  /**
   * Length of a P-384 curve point coordinate in bytes.
   */
  kP384CoordBytes = kP384CoordBits / 8,
  /**
   * Length of a P-384 curve point coordinate in words.
   */
  kP384CoordWords = kP384CoordBytes / sizeof(uint32_t),
  /**
   * Length of an element in the P-384 scalar field (modulo the curve order n).
   */
  kP384ScalarBits = 384,
  /**
   * Length of a secret scalar share in bytes.
   */
  kP384ScalarBytes = kP384ScalarBits / 8,
  /**
   * Length of secret scalar share in words.
   */
  kP384ScalarWords = kP384ScalarBytes / sizeof(uint32_t),
  /**
   * Length of a masked secret scalar share.
   *
   * This implementation uses extra redundant bits for side-channel protection.
   */
  kP384MaskedScalarShareBits = kP384ScalarBits + 64,
  /**
   * Length of a masked secret scalar share in bytes.
   */
  kP384MaskedScalarShareBytes = kP384MaskedScalarShareBits / 8,
  /**
   * Length of masked secret scalar share in words.
   */
  kP384MaskedScalarShareWords = kP384MaskedScalarShareBytes / sizeof(uint32_t),
};

/**
 * A type that holds a masked value from the P-384 scalar field.
 *
 * This struct is used to represent secret keys, which are integers modulo n.
 * The key d is represented in two 320-bit shares, d0 and d1, such that d = (d0
 * + d1) mod n. Mathematically, d0 and d1 could also be reduced modulo n, but
 * the extra bits provide side-channel protection.
 */
typedef struct p384_masked_scalar {
  /**
   * First share of the secret scalar.
   */
  uint32_t share0[kP384MaskedScalarShareWords];
  /**
   * Second share of the secret scalar.
   */
  uint32_t share1[kP384MaskedScalarShareWords];
} p384_masked_scalar_t;

/**
 * A type that holds a P-384 curve point.
 */
typedef struct p384_point {
  /**
   * Affine x-coordinate.
   */
  uint32_t x[kP384CoordWords];
  /**
   * Affine y-coordinate.
   */
  uint32_t y[kP384CoordWords];
} p384_point_t;

/**
 * A type that holds an ECDSA/P-384 signature.
 *
 * The signature consists of two integers r and s, computed modulo n.
 */
typedef struct ecdsa_p384_signature_t {
  uint32_t r[kP384ScalarWords];
  uint32_t s[kP384ScalarWords];
} ecdsa_p384_signature_t;

/**
 * Write a masked P-384 scalar to OTBN's data memory.
 *
 * OTBN actually requires that 512 bits be written, even though only 320 are
 * used; the others are ignored but must be set to avoid an error when OTBN
 * attempts to read uninitialized memory.
 *
 * @param src Masked scalar to write.
 * @param share0_addr DMEM address of the first share.
 * @param share1_addr DMEM address of the second share.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t p384_masked_scalar_write(const p384_masked_scalar_t *src,
                                  const otbn_addr_t share0_addr,
                                  const otbn_addr_t share1_addr);

/**
 * Set the message digest for signature generation or verification.
 *
 * OTBN requires the digest in little-endian form, so this routine flips the
 * bytes.
 *
 * @param digest Digest to set (big-endian).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t set_message_digest(const uint32_t digest[kP384ScalarWords],
                            const otbn_addr_t kOtbnVarEcdsaMsg);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_COMMON_H_
