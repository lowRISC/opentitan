// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_SIGNATURE_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_SIGNATURE_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * RSA signature padding scheme.
 *
 * Schemes are defined in IETF RFC 8017:
 *   https://www.rfc-editor.org/rfc/rfc8017
 *
 * In PSS padding mode, the mask generation function (MGF) is determined by the
 * hash function used for the message:
 * - If the message is hashed with a SHA-2 or SHA-3 hash function, PSS padding
 *   will use MGF1 with the same hash function.
 * - If the message is hashed with a SHAKE128 or SHAKE256 XOF, PSS padding will
 *   use the same XOF as the MGF, as described in FIPS 186-5.
 *
 * Values in this enum should match the top-level `otcrypto_rsa_padding` enum
 * from `sw/device/lib/crypto/include/rsa.h`.
 */
typedef enum rsa_signature_padding {
  // EMSA-PKCS1-v1_5 padding (RFC 8017, section 9.2).
  kRsaSignaturePaddingPkcs1v15 = 0x94e,
  // EMCS-PSS padding (RFC 8017, section 9.1).
  kRsaSignaturePaddingPss = 0x6b1,
} rsa_signature_padding_t;

/**
 * Starts generating an RSA signature; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param size RSA size parameter (e.g. 2048, 3072, 4096).
 * @param d0 RSA private exponent share 0.
 * @param d1 RSA private exponent share 1.
 * @param n RSA public modulus.
 * @param message_digest Message digest to sign.
 * @param padding_mode Signature padding mode.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_signature_generate_start(
    rsa_size_t size, const uint32_t *d0, const uint32_t *d1, const uint32_t *n,
    const otcrypto_hash_digest_t message_digest,
    const rsa_signature_padding_t padding_mode);

/**
 * Waits for an RSA signature generation to complete.
 *
 * Should be invoked only after `rsa_signature_generate_start`. Blocks until
 * OTBN is done processing.
 *
 * @param size RSA size parameter (e.g. 2048, 3072, 4096).
 * @param[out] signature Generated signature.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_signature_generate_finalize(rsa_size_t size, uint32_t *signature);

/**
 * Starts verifying an RSA signature; returns immediately.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param size RSA size parameter (e.g. 2048, 3072, 4096).
 * @param n RSA public modulus.
 * @param signature Signature to verify.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_signature_verify_start(rsa_size_t size, const uint32_t *n,
                                    const uint32_t *signature);

/**
 * Waits for any RSA signature verification to complete.
 *
 * Should be invoked only after a `rsa_signature_verify_start` call, but
 * can be invoked for any size. Blocks until OTBN is done processing, and then
 * infers the size from the OTBN application mode.
 *
 * The caller must check the `result` parameter to see if the signature passed
 * or failed verification; the return value of this function will always return
 * OK unless there are operational errors while running the verification and
 * reading back the result.
 *
 * @param message_digest Message digest to verify the signature against.
 * @param padding_mode Signature padding mode.
 * @param[out] verification_result Whether verification succeeded or failed.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_signature_verify_finalize(
    const otcrypto_hash_digest_t message_digest,
    const rsa_signature_padding_t padding_mode,
    hardened_bool_t *verification_result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_SIGNATURE_H_
