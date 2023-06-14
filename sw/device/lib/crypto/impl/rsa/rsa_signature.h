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

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * RSA signature padding scheme.
 *
 * Schemes are defined in IETF RFC 8017:
 *   https://www.rfc-editor.org/rfc/rfc8017
 *
 * Values in this enum should match the top-level `rsa_padding` enum from
 * `sw/device/lib/crypto/include/rsa.h`.
 */
typedef enum rsa_signature_padding {
  // EMSA-PKCS1-v1_5 padding (RFC 8017, section 9.2).
  kRsaSignaturePaddingPkcs1v15 = 0x9f44,
  // EMCS-PSS padding (RFC 8017, section 9.1).
  kRsaSignaturePaddingPss = 0x88cf,
} rsa_signature_padding_t;

/**
 * Hash function options for RSA signatures.
 *
 * Values in this enum should match the top-level `rsa_hash` enum from
 * `sw/device/lib/crypto/include/rsa.h`.
 */
typedef enum rsa_signature_hash {
  kRsaSignatureHashSha256 = 0xed4b,
  kRsaSignatureHashSha384 = 0x5dd0,
  kRsaSignatureHashSha512 = 0x0bab,
} rsa_signature_hash_t;

/**
 * Starts generating an RSA-2048 signature; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key RSA private key.
 * @param message Message to sign.
 * @param message_len Message length in bytes.
 * @param padding_mode Signature padding mode.
 * @param hash_mode Hash function to use.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_generate_2048_start(
    const rsa_2048_private_key_t *private_key, const uint8_t *message,
    const size_t message_len, const rsa_signature_padding_t padding_mode,
    const rsa_signature_hash_t hash_mode);

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
 * Waits for an RSA-2048 signature generation to complete.
 *
 * Should be invoked only after `rsa_2048_signature_verify_start`. Blocks until
 * OTBN is done processing.
 *
 * The caller must check the `result` parameter to see if the signature passed
 * or failed verification; the return value of this function will always return
 * OK unless there are operational errors while running the verification and
 * reading back the result.
 *
 * @param message Message to verify the signature against.
 * @param message_len Message length in bytes.
 * @param padding_mode Signature padding mode.
 * @param hash_mode Hash function to use.
 * @param[out] verification_result Whether verification succeeded or failed.
 * @return Result of the operation (OK or error).
 */
status_t rsa_signature_verify_2048_finalize(
    const uint8_t *message, const size_t message_len,
    const rsa_signature_padding_t padding_mode,
    const rsa_signature_hash_t hash_mode, hardened_bool_t *verification_result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_SIGNATURE_H_
