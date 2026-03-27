// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_CURVE25519_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_CURVE25519_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Number of words needed to encode a mode of operation.
   */
  kCurve25519ModeWords = 1,
  /**
   * Number of words needed to encode the verification result.
   */
  kCurve25519ResultWords = 1,
  /**
   * Number of words needed to hold an encoded point for Curve25519.
   */
  kCurve25519PointWords = 8,
  /**
   * Number of bytes needed to hold an encoded point for Curve25519.
   */
  kCurve25519PointBytes = kCurve25519PointWords * 4,
  /**
   * Number of bytes needed to hold a SHA512 hash.
   */
  kCurve25519HashBytes = 64,
  /**
   * Number of words needed to hold a SHA512 hash.
   */
  kCurve25519HashWords = kCurve25519HashBytes / 4,
  /**
   * Number of words needed to hold half of a SHA512 hash.
   */
  kCurve25519HalfHashWords = kCurve25519HashWords / 2,
  /**
   * Number of bytes needed to hold a encoded public or private key.
   */
  kCurve25519KeyBytes = 32,
  /**
   * Number of bytes needed to hold a scalar.
   */
  kCurve25519ScalarBytes = 32,
  /**
   * Number of words needed to hold a scalar.
   */
  kCurve25519ScalarWords = kCurve25519ScalarBytes / 4,
  /**
   * Magic value for verify success response.
   */
  kCurve25519VerifySuccess = 0xf77fe650,
};

/**
 * A type that holds an Ed25519 signature.
 *
 * The signature consists of a curve point R and a scalar S.
 */
typedef struct curve25519_signature_t {
  uint32_t r[kCurve25519PointWords];
  uint32_t s[kCurve25519ScalarWords];
} curve25519_signature_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_CURVE25519_H_
