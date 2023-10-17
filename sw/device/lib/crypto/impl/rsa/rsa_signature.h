// Copyright lowRISC contributors.
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
 * Values in this enum should match the top-level `rsa_padding` enum from
 * `sw/device/lib/crypto/include/rsa.h`.
 */
typedef enum rsa_signature_padding {
  // EMSA-PKCS1-v1_5 padding (RFC 8017, section 9.2).
  kRsaSignaturePaddingPkcs1v15 = 0x94e,
  // EMCS-PSS padding (RFC 8017, section 9.1).
  kRsaSignaturePaddingPss = 0x6b1,
} rsa_signature_padding_t;

/**
 * Starts generating an RSA-2048 signature; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key RSA private key.
 * @param message_digest Message digest to sign.
 * @param padding_mode Signature padding mode.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_generate_2048_start(
    const rsa_2048_private_key_t *private_key,
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode);

/**
 * Waits for an RSA-2048 signature generation to complete.
 *
 * Should be invoked only after `rsa_2048_sign_start`. Blocks until OTBN is
 * done processing.
 *
 * @param[out] signature Generated signature.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_generate_2048_finalize(rsa_2048_int_t *signature);

/**
 * Starts verifying an RSA-2048 signature; returns immediately.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key RSA public key.
 * @param signature Signature to verify.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_verify_2048_start(
    const rsa_2048_public_key_t *public_key, const rsa_2048_int_t *signature);

/**
 * Waits for any RSA signature verification to complete.
 *
 * Should be invoked only after a `rsa_signature_verify_{size}_start` call, but
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
status_t rsa_signature_verify_finalize(
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode,
    hardened_bool_t *verification_result);

/**
 * Starts generating an RSA-3072 signature; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key RSA private key.
 * @param message_digest Message digest to sign.
 * @param padding_mode Signature padding mode.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_generate_3072_start(
    const rsa_3072_private_key_t *private_key,
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode);

/**
 * Waits for an RSA-3072 signature generation to complete.
 *
 * Should be invoked only after `rsa_3072_sign_start`. Blocks until OTBN is
 * done processing.
 *
 * @param[out] signature Generated signature.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_generate_3072_finalize(rsa_3072_int_t *signature);

/**
 * Starts verifying an RSA-3072 signature; returns immediately.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key RSA public key.
 * @param signature Signature to verify.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_verify_3072_start(
    const rsa_3072_public_key_t *public_key, const rsa_3072_int_t *signature);

/**
 * Starts generating an RSA-4096 signature; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key RSA private key.
 * @param message_digest Message digest to sign.
 * @param padding_mode Signature padding mode.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_generate_4096_start(
    const rsa_4096_private_key_t *private_key,
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode);

/**
 * Waits for an RSA-4096 signature generation to complete.
 *
 * Should be invoked only after `rsa_4096_sign_start`. Blocks until OTBN is
 * done processing.
 *
 * @param[out] signature Generated signature.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_generate_4096_finalize(rsa_4096_int_t *signature);

/**
 * Starts verifying an RSA-4096 signature; returns immediately.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key RSA public key.
 * @param signature Signature to verify.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_verify_4096_start(
    const rsa_4096_public_key_t *public_key, const rsa_4096_int_t *signature);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_SIGNATURE_H_
