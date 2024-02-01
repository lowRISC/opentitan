// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_VERIFY_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_VERIFY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384_common.h"
#include "sw/device/lib/crypto/impl/ecc/p384_curve_point_valid.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Start an async ECDSA/P-384 signature verification operation on OTBN.
 *
 * See the documentation of `ecdsa_p384_verify` for details.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param signature Signature to be verified.
 * @param digest Digest of the message to check the signature against.
 * @param public_key Key to check the signature against.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t ecdsa_p384_verify_start(const ecdsa_p384_signature_t *signature,
                                 const uint32_t digest[kP384ScalarWords],
                                 const p384_point_t *public_key);

/**
 * Finish an async ECDSA/P-384 signature verification operation on OTBN.
 *
 * See the documentation of `ecdsa_p384_verify` for details.
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
 * @param signature Signature to be verified.
 * @param[out] result Output buffer (true if signature is valid, false
 * otherwise)
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t ecdsa_p384_verify_finalize(const ecdsa_p384_signature_t *signature,
                                    hardened_bool_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_VERIFY_H_
