// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_KEYGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_KEYGEN_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Starts an RSA-2048 key generation operation; returns immediately.
 *
 * The key exponent is always F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_2048_start(void);

/**
 * Waits for an RSA-2048 key generation to complete.
 *
 * Should be invoked only after `rsa_keygen_2048_start`. Blocks until OTBN is
 * done processing.
 *
 * @param[out] public_key Generated public key (n, e).
 * @param[out] private_key Generated private key (d, e).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_2048_finalize(rsa_2048_public_key_t *public_key,
                                  rsa_2048_private_key_t *private_key);

/**
 * Starts an RSA-3072 key generation operation; returns immediately.
 *
 * The key exponent is always F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_3072_start(void);

/**
 * Waits for an RSA-3072 key generation to complete.
 *
 * Should be invoked only after `rsa_keygen_3072_start`. Blocks until OTBN is
 * done processing.
 *
 * @param[out] public_key Generated public key (n, e).
 * @param[out] private_key Generated private key (d, e).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_3072_finalize(rsa_3072_public_key_t *public_key,
                                  rsa_3072_private_key_t *private_key);

/**
 * Starts an RSA-4096 key generation operation; returns immediately.
 *
 * The key exponent is always F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_4096_start(void);

/**
 * Waits for an RSA-4096 key generation to complete.
 *
 * Should be invoked only after `rsa_keygen_4096_start`. Blocks until OTBN is
 * done processing.
 *
 * @param[out] public_key Generated public key (n, e).
 * @param[out] private_key Generated private key (d, e).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_4096_finalize(rsa_4096_public_key_t *public_key,
                                  rsa_4096_private_key_t *private_key);

/**
 * Starts an RSA-2048 key-from-cofactor operation; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported. This
 * routine does not perform any checks on the generated keypair (e.g. primality
 * checks or even range checks).
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key Public key (n, e).
 * @param cofactor One of the prime cofactors (p or q).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_from_cofactor_2048_start(
    const rsa_2048_public_key_t *public_key,
    const rsa_2048_cofactor_t *cofactor);

/**
 * Waits for an RSA-2048 key-from-cofactor operation to complete.
 *
 * Should be invoked only after `rsa_keygen_from_cofactor_2048_start`. Blocks
 * until OTBN is done processing.
 *
 * The public key returned by this function is recomputed by OTBN; callers may
 * find it helpful to compare the public key modulus returned to the one that
 * was passed to OTBN originally in order to check for errors.
 *
 * @param[out] public_key Generated public key (n, e).
 * @param[out] private_key Generated private key (d, e).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_from_cofactor_2048_finalize(
    rsa_2048_public_key_t *public_key, rsa_2048_private_key_t *private_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_KEYGEN_H_
