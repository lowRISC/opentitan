// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_MLDSA_MLDSA_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_MLDSA_MLDSA_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of c_tilde_prime, signature equality check value (in 32-bit words).
   */
  kMldsa87CTildePrimeWords = 16,

  kMldsa87CTildeBytes = 64,
  kMldsa87CTildeWords = kMldsa87CTildeBytes / sizeof(uint32_t),

  kMldsa87ZBytes = 4480,
  kMldsa87ZWords = kMldsa87ZBytes / sizeof(uint32_t),

  kMldsa87HBytes = 83 + 1,
  kMldsa87HWords = kMldsa87HBytes / sizeof(uint32_t),

  kMldsa87SigBytes = 4627 + 1,
  kMldsa87SigWords = kMldsa87SigBytes / sizeof(uint32_t),

  /**
   * 32-bit success and error indicators.
   */
  kMldsa87StatusOk = 0x7baf73d2,
  kMldsa87StatusFail = 0xadf1aebd,
};

/**
 * Redundancy modes for ML-DSA sign.
 */
typedef enum mldsa_sign_redundancy {
  /**
   * Compute a single signature.
   */
  kMldsa87SingleSign = 0x5514edb7,
  /**
   * Compute two signatures and compare that they are equal.
   */
  kMldsa87DoubleSign = 0xfaacd725,
} mldsa_sign_redundancy_t;

/**
 * Start an async ML-DSA-87 signature generation on the OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param secret_key Masked key for the signature generation (6368 bytes).
 * @param rnd The randomness string (32 bytes).
 * @param mu The message hash (64 bytes).
 * @param kappa The rejection loop nonce.
 */
status_t mldsa87_sign_internal_start(const otcrypto_blinded_key_t *secret_key,
                                     const otcrypto_hash_digest_t *mu,
                                     uint32_t mode);

/**
 * Finish an async ML-DSA-87 signature generation on the OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] signature The generated signature (4627 + 1 bytes).
 * @return Result of the operation (OK or error).
 */
status_t mldsa87_sign_internal_finalize(otcrypto_word32_buf_t *signature,
                                        mldsa_sign_redundancy_t redundancy);

/**
 * Start an async ML-DSA-87 signature verification on the OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key Key for the signature verification (2592 bytes).
 * @param signature Signature to be verified (4628 bytes).
 * @param mu The hashed message (64 bytes).
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t mldsa87_verify_internal_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_word32_buf_t *signature,
    const otcrypto_hash_digest_t *mu);

/**
 * Finish an async ML-DSA-87 signature verification on the OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * If the signature is valid, writes `kHardenedBoolTrue` to `result`;
 * otherwise, writes `kHardenedBoolFalse`.
 *
 * Note: the caller must check the `result` buffer in order to determine if a
 * signature passed verification. If a signature is invalid, but nothing goes
 * wrong during computation (e.g. hardware errors, failed preconditions), the
 * status will be OK but `result` will be `kHardenedBoolFalse`.
 *
 * @param signature Signature to be verified (4628 bytes).
 * @param[out] result (true if signature is valid, false otherwise).
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t mldsa87_verify_internal_finalize(
    const otcrypto_const_word32_buf_t *signature, hardened_bool_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_MLDSA_MLDSA_H_
