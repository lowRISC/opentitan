// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_MODEXP_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_MODEXP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Start a constant-time RSA-2048 modular exponentiation.
 *
 * This construct is for secret exponents, and is much slower than the
 * variable-time version.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param base Exponentiation base.
 * @param exp Exponent to raise the base to.
 * @param modulus Modulus for exponentiation.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_consttime_2048_start(const rsa_2048_int_t *base,
                                         const rsa_2048_int_t *exp,
                                         const rsa_2048_int_t *modulus);

/**
 * Start a variable-time RSA-2048 modular exponentiation.
 *
 * Do not use this construct with secret exponents; its timing depends on the
 * exponent.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param base Exponentiation base.
 * @param exp Exponent to raise the base to.
 * @param modulus Modulus for exponentiation.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_vartime_2048_start(const rsa_2048_int_t *base,
                                       const uint32_t exp,
                                       const rsa_2048_int_t *modulus);

/**
 * Waits for an RSA-2048 modular exponentiation to complete.
 *
 * Can be used after either:
 * - `rsa_modexp_consttime_2048_start()`
 * - `rsa_modexp_vartime_2048_start()`
 *
 * @param[out] result Exponentiation result = (base ^ exp) mod modulus.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_2048_finalize(rsa_2048_int_t *result);

/**
 * Start a constant-time RSA-3072 modular exponentiation.
 *
 * This construct is for secret exponents, and is much slower than the
 * variable-time version.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param base Exponentiation base.
 * @param exp Exponent to raise the base to.
 * @param modulus Modulus for exponentiation.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_consttime_3072_start(const rsa_3072_int_t *base,
                                         const rsa_3072_int_t *exp,
                                         const rsa_3072_int_t *modulus);

/**
 * Start a variable-time RSA-3072 modular exponentiation.
 *
 * Do not use this construct with secret exponents; its timing depends on the
 * exponent.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param base Exponentiation base.
 * @param exp Exponent to raise the base to.
 * @param modulus Modulus for exponentiation.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_vartime_3072_start(const rsa_3072_int_t *base,
                                       const uint32_t exp,
                                       const rsa_3072_int_t *modulus);

/**
 * Waits for an RSA-3072 modular exponentiation to complete.
 *
 * Can be used after either:
 * - `rsa_modexp_consttime_3072_start()`
 * - `rsa_modexp_vartime_3072_start()`
 *
 * @param[out] result Exponentiation result = (base ^ exp) mod modulus.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_3072_finalize(rsa_3072_int_t *result);

/**
 * Start a constant-time RSA-4096 modular exponentiation.
 *
 * This construct is for secret exponents, and is much slower than the
 * variable-time version.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param base Exponentiation base.
 * @param exp Exponent to raise the base to.
 * @param modulus Modulus for exponentiation.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_consttime_4096_start(const rsa_4096_int_t *base,
                                         const rsa_4096_int_t *exp,
                                         const rsa_4096_int_t *modulus);

/**
 * Start a variable-time RSA-4096 modular exponentiation.
 *
 * Do not use this construct with secret exponents; its timing depends on the
 * exponent.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param base Exponentiation base.
 * @param exp Exponent to raise the base to.
 * @param modulus Modulus for exponentiation.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_vartime_4096_start(const rsa_4096_int_t *base,
                                       const uint32_t exp,
                                       const rsa_4096_int_t *modulus);

/**
 * Waits for an RSA-4096 modular exponentiation to complete.
 *
 * Can be used after either:
 * - `rsa_modexp_consttime_4096_start()`
 * - `rsa_modexp_vartime_4096_start()`
 *
 * @param[out] result Exponentiation result = (base ^ exp) mod modulus.
 * @return Status of the operation (OK or error).
 */
status_t rsa_modexp_4096_finalize(rsa_4096_int_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_MODEXP_H_
