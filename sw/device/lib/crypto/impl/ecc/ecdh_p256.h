// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDH_P256_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDH_P256_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p256_common.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A type that holds a blinded ECDH shared secret key.
 *
 * The key is boolean-masked (XOR of the two shares).
 */
typedef struct ecdh_p256_shared_key {
  uint32_t share0[kP256CoordWords];
  uint32_t share1[kP256CoordWords];
} ecdh_p256_shared_key_t;

/**
 * Start an async ECDH/P-256 keypair generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
status_t ecdh_p256_keypair_start(void);

/**
 * Finish an async ECDH/P-256 keypair generation operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] private_key Generated private key.
 * @param[out] public_key Generated public key.
 * @return Result of the operation (OK or error).
 */
status_t ecdh_p256_keypair_finalize(p256_masked_scalar_t *private_key,
                                    p256_point_t *public_key);

/**
 * Start an async ECDH/P-256 shared key generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key Private key (d).
 * @param public_key Public key (Q).
 * @return Result of the operation (OK or error).
 */
status_t ecdh_p256_shared_key_start(const p256_masked_scalar_t *private_key,
                                    const p256_point_t *public_key);

/**
 * Finish an async ECDH/P-256 shared key generation operation on OTBN.
 *
 * Blocks until OTBN is idle. May be used after either
 * `ecdh_p256_shared_key_start` or `ecdh_p256_sideload_shared_key_start`; the
 * operation is the same.
 *
 * @param[out] shared_key Shared secret key (x-coordinate of d*Q).
 * @return Result of the operation (OK or error).
 */
status_t ecdh_p256_shared_key_finalize(ecdh_p256_shared_key_t *shared_key);

/**
 * Start an async ECDH/P-256 sideloaded keypair generation operation on OTBN.
 *
 * Generates the keypair from a key manager seed. The key manager should
 * already have sideloaded the key into OTBN before this operation is called.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
status_t ecdh_p256_sideload_keypair_start(void);

/**
 * Finish an async ECDH/P-256 sideloaded keypair generation operation on OTBN.
 *
 * Blocks until OTBN is idle. Returns only the public key.
 *
 * @param[out] public_key Generated public key.
 * @return Result of the operation (OK or error).
 */
status_t ecdh_p256_sideload_keypair_finalize(p256_point_t *public_key);

/**
 * Start an async ECDH/P-256 shared key generation operation on OTBN.
 *
 * Uses a private key generated from a key manager seed. The key manager should
 * already have sideloaded the key into OTBN before this operation is called.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key Public key (Q).
 * @return Result of the operation (OK or error).
 */
status_t ecdh_p256_sideload_shared_key_start(const p256_point_t *public_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDH_P256_H_
