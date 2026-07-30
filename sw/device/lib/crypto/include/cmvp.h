// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CMVP_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CMVP_H_

#include "datatypes.h"

/**
 * @file
 * @brief CMVP service indicator for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Provides the service indicator for the most recently used cryptolib API.
 *
 * Checks if the last called cryptolib function was a CMVP
 * (Cryptographic Module Validation Program) approved service. The result is
 * returned through the `indicator` output parameter.
 * After each call the service indicator is reset to `kOtcryptoCmvpNoService`.
 *
 * @param[out] indicator Pointer to receive the indicator status.
 * @return Result of the operation.
 */
otcrypto_status_t otcrypto_cmvp_service_indicator(
    otcrypto_cmvp_service_indicator_t *indicator);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CMVP_H_
