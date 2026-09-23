// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_HKDF_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_HKDF_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Performs Masked HKDF (Extract + Expand) on OTBN in one step.
 *
 * Uses the dedicated masked OTBN HKDF binaries (`run_hkdf_sha256`,
 * `run_hkdf_sha384`, `run_hkdf_sha512`) when inputs fit single-run OTBN
 * buffers, and falls back to multi-block OTBN masked SHA-2 (`run_sha256`,
 * `run_sha384`, `run_sha512`) for larger messages/outputs.
 *
 * @param ikm Blinded input key material (with HMAC key mode determining hash).
 * @param salt Unmasked salt value (may be empty).
 * @param info Unmasked context/application specific info (may be empty).
 * @param[out] okm Blinded output keying material.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otbn_hkdf(const otcrypto_blinded_key_t *ikm,
                            const otcrypto_const_byte_buf_t *salt,
                            const otcrypto_const_byte_buf_t *info,
                            otcrypto_blinded_key_t *okm);

/**
 * Performs the "extract" step of HKDF on OTBN.
 *
 * @param ikm Blinded input key material.
 * @param salt Unmasked salt value.
 * @param[out] prk Blinded pseudo-random key.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otbn_hkdf_extract(const otcrypto_blinded_key_t *ikm,
                                    const otcrypto_const_byte_buf_t *salt,
                                    otcrypto_blinded_key_t *prk);

/**
 * Performs the "expand" step of HKDF on OTBN.
 *
 * @param prk Blinded pseudo-random key from extract.
 * @param info Unmasked context-specific string.
 * @param[out] okm Blinded output keying material.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otbn_hkdf_expand(const otcrypto_blinded_key_t *prk,
                                   const otcrypto_const_byte_buf_t *info,
                                   otcrypto_blinded_key_t *okm);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_HKDF_H_
