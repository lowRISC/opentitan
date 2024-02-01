// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_KEYGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_KEYGEN_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384_common.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Start an async ECDSA/P-384 keypair generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t ecdsa_p384_keygen_start(void);

/**
 * Finish an async ECDSA/P-384 keypair generation operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] private_key Generated private key.
 * @param[out] public_key Generated public key.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t ecdsa_p384_keygen_finalize(p384_masked_scalar_t *private_key,
                                    p384_point_t *public_key);

#ifdef __cplusplus
}
"C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_KEYGEN_H_
