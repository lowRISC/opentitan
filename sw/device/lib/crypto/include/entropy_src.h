// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ENTROPY_SRC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ENTROPY_SRC_H_

#include "datatypes.h"

/**
 * @file
 * @brief Entropy source functions for the OpenTitan cryptography library.
 *
 * Instantiate and use the TRNG. Acts as a wrapper to the entropy driver.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Configures the entropy source in continuous mode with FIPS thresholds.
 *
 * @return Operation status in `otcrypto_status_t` format.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_entropy_init(void);

/**
 * Ensures that the entropy complex is ready for use and verify the health
 * checks of the generated randomness.
 *
 * Ensures that the entropy complex is running and that `entropy_src` is in
 * FIPS mode, and verifies the thresholds for health tests in `entropy_src`.
 * This function should be called periodically while the entropy complex is in
 * use, because the threshold registers are not shadowed.
 *
 * The test also verifies the health checks of the generated randomness
 * providing a status error if a health test jumped.
 *
 * @return Operation status in `otcrypto_status_t` format.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_entropy_check(void);

/**
 * Check the entropy complex health test and alert configurations.
 *
 * This function checks the entropy src registers to detect tampering.
 * The multi-bit encoded registers are checked by the HW.
 *
 * This function does not return a status error, and will simply assert the chip
 * is in the correct configuration.
 *
 * @return Operation status in `otcrypto_status_t` format.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_entropy_health_test_config_check(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ENTROPY_SRC_H_
