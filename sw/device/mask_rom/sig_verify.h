// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_MASK_ROM_SIG_VERIFY_H_
#define OPENTITAN_SW_DEVICE_MASK_ROM_SIG_VERIFY_H_

// TODO: Will we have doc pages for mask ROM modules?
/**
 * @file
 * @brief Mask ROM <a href="">Signature Verification</a> Module
 */

// TODO: Doxygen comments.

#include "sw/device/lib/base/mmio.h"
// TODO: We probably want WARN_UNUSED_RESULT for mask_rom modules too.
#include <stddef.h>
#include <stdint.h>

// TODO: Remove this once ROM_EXT manifest is available.
#include "sw/device/mask_rom/rom_ext_manifest.h"

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// TODO: Return codes and error handling: #3385
/**
 * Common return codes for the functions in this module.
 */
typedef enum sig_verify_result {
  /**
   * Indicates that the call succeeded.
   */
  kSigVerifyOk = 0,
  /**
   * Indicates that an unexpected error occurred.
   */
  kSigVerifyError = 1,
} sig_verify_result_t;

/**
 * Supported hash algorithms.
 */
typedef enum sig_verify_hash_alg {
  kSigVerifyHashAlgSha2_256,
  kSigVerifyHashAlgSha2_384,
  kSigVerifyHashAlgSha2_512,
} sig_verify_hash_alg_t;

/**
 * A digest.
 */
typedef struct sig_verify_digest {
  sig_verify_hash_alg_t alg;
  union {
    uint8_t sha2_256[32];
    uint8_t sha2_384[48];
    uint8_t sha2_512[64];
  };
} sig_verify_digest_t;

/**
 * Verify the signature of a ROM_EXT manifest.
 * Note: `actual` and `expected` are digests that can be used by the Secure Boot
 * HW Support.
 */
sig_verify_result_t sig_verify_verify_rom_ext(
    const rom_ext_manifest_t *manifest, bool *is_valid,
    sig_verify_digest_t *actual, sig_verify_digest_t *expected);

/**
 * Get the digest buffer and length from a `sig_verify_digest_t`. Since this
 * returns a pointer to contents of a `sig_verify_digest_t`, clients must make
 * sure that the pointer does not outlive that struct.
 */
sig_verify_result_t sig_verify_get_digest_value(
    const sig_verify_digest_t *digest, const uint8_t **value, size_t *length);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_MASK_ROM_SIG_VERIFY_H_
