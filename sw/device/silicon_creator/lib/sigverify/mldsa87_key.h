// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MLDSA87_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MLDSA87_KEY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of a ML-DSA-87 public key.
   */
  kSigverifyMldsa87PkBytes = 2592,
  kSigverifyMldsa87PkWords = kSigverifyMldsa87PkBytes / sizeof(uint32_t),
  /**
   * Size of a ML-DSA-87 signature. It is stored zero-padded to a whole number
   * of words.
   */
  kSigverifyMldsa87SigBytes = 4627,
  kSigverifyMldsa87SigWords =
      (kSigverifyMldsa87SigBytes + sizeof(uint32_t) - 1) / sizeof(uint32_t),
};

/**
 * Context string of the ML-DSA-87 image signature (FIPS 204, pure mode).
 *
 * Must match `MLDSA87_IMAGE_CONTEXT` in
 * `sw/host/opentitanlib/src/image/manifest.rs`.
 */
extern const uint8_t kSigverifyMldsa87ImageContext[];
extern const size_t kSigverifyMldsa87ImageContextSize;

/**
 * An ML-DSA-87 signature.
 */
typedef struct sigverify_mldsa87_signature {
  uint32_t data[kSigverifyMldsa87SigWords];
} sigverify_mldsa87_signature_t;

/**
 * An ML-DSA-87 public key.
 */
typedef struct sigverify_mldsa87_key {
  uint32_t data[kSigverifyMldsa87PkWords];
} sigverify_mldsa87_key_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MLDSA87_KEY_H_
