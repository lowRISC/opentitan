// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RUN_RSA_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RUN_RSA_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Block until a modexp operation is complete and get the result size.
 *
 * After OTBN finishes processing, this function reads the mode and infers the
 * size of the modulus/signature for the just-finished operation. It then
 * populates the `num_words` parameter with this size (expressed in 32b words).
 * This is designed so that callers can call `rsa_modexp_wait()` and then use
 * the size to select the appropriate `finalize()` call.
 *
 * @param[out] num_words Number of words for result buffers.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_wait(size_t *num_words);

/**
 * Start a constant-time RSA modular exponentiation.
 *
 * This construct is for secret exponents, and is much slower than the
 * variable-time version.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param size RSA size parameter (e.g. 2048, 3072, 4096).
 * @param base Exponentiation base.
 * @param exp0 Exponent to raise the base to (share 0).
 * @param exp1 Exponent to raise the base to (share 1).
 * @param modulus Modulus for exponentiation.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_consttime_start(rsa_size_t size, const uint32_t *base,
                                    const uint32_t *exp0, const uint32_t *exp1,
                                    const uint32_t *modulus);

/**
 * Start a variable-time RSA modular exponentiation.
 *
 * Do not use this construct with secret exponents; its timing depends on the
 * exponent.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param size RSA size parameter (e.g. 2048, 3072, 4096).
 * @param base Exponentiation base.
 * @param modulus Modulus for exponentiation.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_vartime_start(rsa_size_t size, const uint32_t *base,
                                  const uint32_t *modulus);

/**
 * Waits for an RSA modular exponentiation to complete.
 *
 * Can be used after either:
 * - `rsa_modexp_consttime_start()`
 * - `rsa_modexp_vartime_start()`
 *
 * @param size RSA size parameter (e.g. 2048, 3072, 4096).
 * @param[out] result Exponentiation result = (base ^ exp) mod modulus.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_finalize_size(rsa_size_t size, uint32_t *result);

/**
 * Starts an RSA key generation operation; returns immediately.
 *
 * The key exponent is always F4=65537; no other exponents are supported.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param size RSA size parameter (e.g. 2048, 3072, 4096).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_start(rsa_size_t size);

/**
 * Waits for an RSA key generation to complete.
 *
 * Should be invoked only after `rsa_keygen_start`. Blocks until OTBN is
 * done processing.
 *
 * @param size RSA size parameter (e.g. 2048, 3072, 4096).
 * @param[out] n Generated public key modulus (n).
 * @param[out] d0 Generated private key exponent share 0 (d0).
 * @param[out] d1 Generated private key exponent share 1 (d1).
 * @return Result of the operation (OK or error).
 */
status_t rsa_keygen_finalize_size(rsa_size_t size, uint32_t *n, uint32_t *d0,
                                  uint32_t *d1);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RUN_RSA_H_
