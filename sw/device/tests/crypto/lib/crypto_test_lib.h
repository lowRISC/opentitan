// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_LIB_CRYPTO_TEST_LIB_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_LIB_CRYPTO_TEST_LIB_H_

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Determine the security level we can use on the device.
 *
 * As some ROMs disable some of the security features the CL requires for some
 * security levels, check if they are available or not. If they are not
 * available, use kOtcryptoKeySecurityLevelLow, if all of them are available,
 * randomly select one of kOtcryptoKeySecurityLevelLow,
 * kOtcryptoKeySecurityLevelMedium, or kOtcryptoKeySecurityLevelHigh.
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
