// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_CURVE_POINT_VALID_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_CURVE_POINT_VALID_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384_common.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Start a P-384 public key (curve point) validation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 * Returns an `ILLEGAL_INSN` error if public key (curve point) is invalid.
 *
 * @param public_key Public key (Q).
 * @return Result of the operation (OK or error).
 */
status_t p384_curve_point_validate_start(const p384_point_t *public_key);

/**
 * Finish a P-384 public key (curve point) validation operation on OTBN.
 *
 * Blocks until OTBN is idle. To be used after `p384_curve_point_validate`.
 *
 * @return Result of the operation (OK or error).
 */
status_t p384_curve_point_validate_finalize(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_CURVE_POINT_VALID_H_
