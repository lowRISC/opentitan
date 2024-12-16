// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_X25519_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_X25519_H_

#include "datatypes.h"

/**
 * @file
 * @brief X25519 operations for OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Generates a key pair for X25519.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. For a hardware-backed key, use the private key handle returned by
 * `otcrypto_hw_backed_key`. Otherwise, the mode should indicate X25519 and the
 * keyblob should be 80 bytes. The value in the `checksum` field of the blinded
 * key struct will be populated by the key generation function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the X25519 key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen(otcrypto_blinded_key_t *private_key,
                                         otcrypto_unblinded_key_t *public_key);

/**
 * Elliptic-curve Diffie Hellman shared secret generation with Curve25519.
 *
 * @param private_key Pointer to blinded private key (u-coordinate).
 * @param public_key Pointer to the public scalar from the sender.
 * @param[out] shared_secret Pointer to shared secret key (u-coordinate).
 * @return Result of the X25519 operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519(const otcrypto_blinded_key_t *private_key,
                                  const otcrypto_unblinded_key_t *public_key,
                                  otcrypto_blinded_key_t *shared_secret);

/**
 * Starts asynchronous key generation for X25519.
 *
 * See `otcrypto_x25519_keygen` for requirements on input values.
 *
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous X25519 keygen start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen_async_start(
    const otcrypto_blinded_key_t *private_key);

/**
 * Finalizes the asynchronous key generation for X25519.
 *
 * See `otcrypto_x25519_keygen` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * The caller should ensure that the private key configuration matches that
 * passed to the `_start` function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous ECDSA keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous shared secret generation for X25519.
 *
 * See `otcrypto_x25519` for requirements on input values.
 *
 * @param private_key Pointer to the blinded private key (u-coordinate).
 * @param public_key Pointer to the public scalar from the sender.
 * @return Result of the async X25519 start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key);

/**
 * Finalizes asynchronous shared secret generation for X25519.
 *
 * See `otcrypto_x25519` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param[out] shared_secret Pointer to shared secret key (u-coordinate).
 * @return Result of async X25519 finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_async_finalize(
    otcrypto_blinded_key_t *shared_secret);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_X25519_H_
