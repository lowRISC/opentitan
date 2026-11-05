// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HMAC_DRBG_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HMAC_DRBG_H_

#include "datatypes.h"

/**
 * @file
 * @brief HMAC-DRBG (NIST SP 800-90Ar1 Section 10.1.2) for the OpenTitan
 * cryptography library.
 *
 * WARNING: This module is NOT protected against fault injection (FI) or
 * side-channel analysis (SCA) attacks.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of the HMAC-DRBG context in 32-bit words.
   */
  kOtcryptoHmacDrbgCtxStructWords = 54,
  /**
   * Minimum entropy and nonce input length in bytes.
   */
  kOtcryptoHmacDrbgMinEntropyBytes = 1,
  kOtcryptoHmacDrbgMinNonceBytes = 1,
  /**
   * Maximum output size in bytes per generate request (2^19 bits, per NIST SP
   * 800-90Ar1 Table 2).
   */
  kOtcryptoHmacDrbgMaxOutputBytes = 65536,
};

/**
 * Opaque HMAC-DRBG context.
 *
 * Representation is internal to the HMAC-DRBG implementation; initialize with
 * #otcrypto_hmac_drbg_init.
 */
typedef struct otcrypto_hmac_drbg_context {
  /// HMAC-DRBG internal context.
  uint32_t data[kOtcryptoHmacDrbgCtxStructWords];
} otcrypto_hmac_drbg_context_t;

/**
 * Initializes an HMAC-DRBG context.
 *
 * Instantiates the HMAC-DRBG state (K, V, and reseed counter) using the
 * caller-supplied `entropy`, `nonce`, and `perso_string` inputs with the
 * selected SHA-2 `hash_mode` (`kOtcryptoHashModeSha256`,
 * `kOtcryptoHashModeSha384`, or `kOtcryptoHashModeSha512`). Auto-reseed is
 * disabled by default upon initialization.
 *
 * WARNING: This function is part of the HMAC-DRBG implementation and is NOT
 * protected against fault injection (FI) or side-channel analysis (SCA)
 * attacks.
 *
 * @param[out] ctx Pointer to the HMAC-DRBG context struct to initialize.
 * @param entropy Provided entropy input (must be at least
 * `kOtcryptoHmacDrbgMinEntropyBytes` bytes; NIST SP 800-90Ar1 Table 2
 * recommends at least `security_strength` bytes).
 * @param nonce Provided nonce input (must be at least
 * `kOtcryptoHmacDrbgMinNonceBytes` bytes; NIST SP 800-90Ar1 Table 2 recommends
 * at least `security_strength / 2` bytes).
 * @param perso_string Provided personalization string (may be empty, i.e. 0
 * bytes).
 * @param reseed_interval Reseed interval in generate calls (must be > 0).
 * @param hash_mode Underlying SHA-2 hash mode (`kOtcryptoHashModeSha256`,
 * `kOtcryptoHashModeSha384`, or `kOtcryptoHashModeSha512`).
 * @return Result of the HMAC-DRBG init operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or `hash_mode` are invalid, or `kOtcryptoStatusValueFatalError` if
 * an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_drbg_init(
    otcrypto_hmac_drbg_context_t *ctx, const otcrypto_const_byte_buf_t *entropy,
    const otcrypto_const_byte_buf_t *nonce,
    const otcrypto_const_byte_buf_t *perso_string, uint32_t reseed_interval,
    otcrypto_hash_mode_t hash_mode);

/**
 * Deinitializes and shreds an HMAC-DRBG context.
 *
 * WARNING: This function is part of the HMAC-DRBG implementation and is NOT
 * protected against fault injection (FI) or side-channel analysis (SCA)
 * attacks.
 *
 * @param ctx Pointer to the HMAC-DRBG context struct to deinitialize.
 * @return Result of the HMAC-DRBG deinit operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if `ctx`
 * is NULL, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_drbg_deinit(otcrypto_hmac_drbg_context_t *ctx);

/**
 * Reseeds an initialized HMAC-DRBG context.
 *
 * Updates the internal working state (K, V) with the provided `entropy` and
 * optional `additional_input`, and resets the reseed counter to 1.
 *
 * #otcrypto_hmac_drbg_init should be called before calling this function.
 *
 * WARNING: This function is part of the HMAC-DRBG implementation and is NOT
 * protected against fault injection (FI) or side-channel analysis (SCA)
 * attacks.
 *
 * @param ctx Pointer to an initialized HMAC-DRBG context struct.
 * @param entropy Provided entropy input (must be at least
 * `kOtcryptoHmacDrbgMinEntropyBytes` bytes).
 * @param additional_input Additional input string (may be empty, i.e. 0
 * bytes).
 * @return Result of the HMAC-DRBG reseed operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid or `ctx` is uninitialized, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_drbg_reseed(
    otcrypto_hmac_drbg_context_t *ctx, const otcrypto_const_byte_buf_t *entropy,
    const otcrypto_const_byte_buf_t *additional_input);

/**
 * Enables or disables automatic reseeding for an HMAC-DRBG context.
 *
 * When auto-reseed is enabled (`kHardenedBoolTrue`), calling
 * #otcrypto_hmac_drbg_generate when the reseed counter exceeds
 * `reseed_interval` will automatically fetch fresh entropy from the hardware
 * DRBG and reseed the context. When disabled (`kHardenedBoolFalse`),
 * #otcrypto_hmac_drbg_generate will return `kOtcryptoStatusValueRecovError` if
 * a reseed is required.
 *
 * #otcrypto_hmac_drbg_init should be called before calling this function.
 *
 * WARNING: This function is part of the HMAC-DRBG implementation and is NOT
 * protected against fault injection (FI) or side-channel analysis (SCA)
 * attacks.
 *
 * @param ctx Pointer to an initialized HMAC-DRBG context struct.
 * @param enabled `kHardenedBoolTrue` to enable, `kHardenedBoolFalse` to
 * disable.
 * @return Result of the operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments are invalid or `ctx` is
 * uninitialized, or `kOtcryptoStatusValueFatalError` if an internal hardware
 * check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_drbg_set_auto_reseed(
    otcrypto_hmac_drbg_context_t *ctx, hardened_bool_t enabled);

/**
 * Generates pseudo-random bytes from an initialized HMAC-DRBG context.
 *
 * Generates `drbg_output->len` bytes (up to `kOtcryptoHmacDrbgMaxOutputBytes`)
 * and updates the internal state and reseed counter.
 *
 * #otcrypto_hmac_drbg_init should be called before calling this function.
 *
 * WARNING: This function is part of the HMAC-DRBG implementation and is NOT
 * protected against fault injection (FI) or side-channel analysis (SCA)
 * attacks.
 *
 * @param ctx Pointer to an initialized HMAC-DRBG context struct.
 * @param additional_input Optional additional input (may be empty, i.e. 0
 * bytes).
 * @param[out] drbg_output Output buffer for generated pseudo-random bytes (up
 * to `kOtcryptoHmacDrbgMaxOutputBytes` bytes).
 * @return Result of the HMAC-DRBG generate operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or output length are invalid or `ctx` is uninitialized,
 * `kOtcryptoStatusValueRecovError` if a reseed is required and auto-reseed is
 * disabled, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_drbg_generate(
    otcrypto_hmac_drbg_context_t *ctx,
    const otcrypto_const_byte_buf_t *additional_input,
    otcrypto_byte_buf_t *drbg_output);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HMAC_DRBG_H_
