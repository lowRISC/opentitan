// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_SIGN_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_SIGN_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384_common.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

extern otbn_addr_t kOtbnVarEcdsaR;
extern otbn_addr_t kOtbnVarEcdsaS;

/**
 * Start an async ECDSA/P-384 signature generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param digest Digest of the message to sign.
 * @param private_key Secret key to sign the message with.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t ecdsa_p384_sign_start(const uint32_t digest[kP384ScalarWords],
                               const p384_masked_scalar_t *private_key);

/**
 * Finish an async ECDSA/P-384 signature generation operation on OTBN.
 *
 * See the documentation of `ecdsa_p384_sign` for details.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] result Buffer in which to store the generated signature.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t ecdsa_p384_sign_finalize(ecdsa_p384_signature_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P384_SIGN_H_
