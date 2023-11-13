// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_sm2_COMMON_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_sm2_COMMON_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Length of a P-256 curve point coordinate in bits (modulo p).
   */
  ksm2CoordBits = 256,
  /**
   * Length of a P-256 curve point coordinate in bytes.
   */
  ksm2CoordBytes = ksm2CoordBits / 8,
  /**
   * Length of a P-256 curve point coordinate in words.
   */
  ksm2CoordWords = ksm2CoordBytes / sizeof(uint32_t),
  /**
   * Length of an element in the P-256 scalar field (modulo the curve order n).
   */
  ksm2ScalarBits = 256,
  /**
   * Length of a secret scalar share in bytes.
   */
  ksm2ScalarBytes = ksm2ScalarBits / 8,
  /**
   * Length of secret scalar share in words.
   */
  ksm2ScalarWords = ksm2ScalarBytes / sizeof(uint32_t),
  /**
   * Length of a masked secret scalar share.
   *
   * This implementation uses extra redundant bits for side-channel protection.
   */
  ksm2MaskedScalarShareBits = ksm2ScalarBits + 64,
  /**
   * Length of a masked secret scalar share in bytes.
   */
  ksm2MaskedScalarShareBytes = ksm2MaskedScalarShareBits / 8,
  /**
   * Length of masked secret scalar share in words.
   */
  ksm2MaskedScalarShareWords = ksm2MaskedScalarShareBytes / sizeof(uint32_t),
};

/**
 * A type that holds a masked value from the P-256 scalar field.
 *
 * This struct is used to represent secret keys, which are integers modulo n.
 * The key d is represented in two 320-bit shares, d0 and d1, such that d = (d0
 * + d1) mod n. Mathematically, d0 and d1 could also be reduced modulo n, but
 * the extra bits provide side-channel protection.
 */
typedef struct sm2_masked_scalar {
  /**
   * First share of the secret scalar.
   */
  uint32_t share0[ksm2MaskedScalarShareWords];
  /**
   * Second share of the secret scalar.
   */
  uint32_t share1[ksm2MaskedScalarShareWords];
} sm2_masked_scalar_t;

/**
 * A type that holds a P-256 curve point.
 */
typedef struct sm2_point {
  /**
   * Affine x-coordinate.
   */
  uint32_t x[ksm2CoordWords];
  /**
   * Affine y-coordinate.
   */
  uint32_t y[ksm2CoordWords];
} sm2_point_t;

/**
 * Write a masked P-256 scalar to OTBN's data memory.
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
status_t sm2_masked_scalar_write(const sm2_masked_scalar_t *src,
                                  const otbn_addr_t share0_addr,
                                  const otbn_addr_t share1_addr);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_sm2_COMMON_H_
