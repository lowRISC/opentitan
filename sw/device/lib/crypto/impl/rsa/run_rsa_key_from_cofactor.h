// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RUN_RSA_KEY_FROM_COFACTOR_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RUN_RSA_KEY_FROM_COFACTOR_H_

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
 * Starts an RSA key-from-cofactor operation; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported. This
 * routine does not perform any checks on the generated keypair (e.g. primality
 * checks or even range checks).
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param size RSA size parameter (e.g., 2048, 3072, 4096).
 * @param public_key_n Public key modulus (n).
 * @param cofactor One of the prime cofactors (p or q).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_from_cofactor_start(rsa_size_t size,
                                        const uint32_t *public_key_n,
                                        const uint32_t *cofactor);

/**
 * Waits for an RSA key-from-cofactor operation to complete.
 *
 * Should be invoked only after `rsa_keygen_from_cofactor_start`. Blocks
 * until OTBN is done processing.
 *
 * The public key returned by this function is recomputed by OTBN; callers may
 * find it helpful to compare the public key modulus returned to the one that
 * was passed to OTBN originally in order to check for errors.
 *
 * @param size RSA size parameter (e.g., 2048, 3072, 4096).
 * @param[out] public_key_n Generated public key modulus (n).
 * @param[out] private_key_n Generated private key modulus (n).
 * @param[out] private_key_d0 Generated private key exponent share 0 (d0).
 * @param[out] private_key_d1 Generated private key exponent share 1 (d1).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_from_cofactor_finalize(rsa_size_t size,
                                           uint32_t *public_key_n,
                                           uint32_t *private_key_n,
                                           uint32_t *private_key_d0,
                                           uint32_t *private_key_d1);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RUN_RSA_KEY_FROM_COFACTOR_H_
