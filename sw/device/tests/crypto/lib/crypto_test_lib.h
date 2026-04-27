// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_LIB_CRYPTO_TEST_LIB_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_LIB_CRYPTO_TEST_LIB_H_

#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// Available security levels. The test randomly chooses one.
static const otcrypto_key_security_level_t available_security_levels[3] = {
    kOtcryptoKeySecurityLevelLow,
    kOtcryptoKeySecurityLevelMedium,
    kOtcryptoKeySecurityLevelHigh,
};

/**
 * Determine a random security level.
 *
 * @param[out] security_level Cycle count for the decrypt() call
 * @return OK or error.
 */
status_t determine_security_level(
    otcrypto_key_security_level_t *security_level);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_LIB_CRYPTO_TEST_LIB_H_
