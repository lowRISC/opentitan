// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CONFIG_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CONFIG_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Check if the chip is in a secure configuration state.
 *
 * Returns OK if the jittery clock, the dummy instructions, and the data
 * independent timing is enabled.
 *
 * @param security_level Security level of the used key.
 * @returns OK when the security check passed.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_security_config_check(
    otcrypto_key_security_level_t security_level);

/**
 * Set the chip in a secure configuration state.
 *
 * On non-low security level, enables the jittery clock, the dummy instructions,
 * and the data independent timing. On low security level, leaves the chip as it
 * is.
 *
 * This function writes to Ibex registers. Hence, it is only usable in M mode.
 *
 * @param security_level Security level of the used key.
 * @returns OK when the configuration is correctly set.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_set_security_config(
    otcrypto_key_security_level_t security_level);

/**
 * Disable the Ibex Instruction Cache if it is enabled.
 *
 * Reads out the current state of the instruction cache. If it is enabled,
 * disable it for the crypto lib.
 * It is only usable in M mode.
 *
 * @param[out] icache_enabled kHardenedBoolTrue if the iCache was enabled before
 * we disabled it.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_disable_icache(hardened_bool_t *icache_enabled);

/**
 * Enables the Ibex Instruction Cache if icache_enabled is set.
 *
 * If icache_enabled == kHardenedBoolTrue, this function enables the iCache by
 * writing to CPUCTRL.
 * It is only usable in M mode.
 *
 * @param icache_enabled kHardenedBoolTrue to enable the iCache.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_restore_icache(hardened_bool_t icache_enabled);

/**
 * Clear the alerts including local alerts and sensors.
 *
 * The cryptolib locks itself when there is a class (A,B,C,D) acumulation count
 * higher than zero or when a local alert or sensor is triggered. This function
 * reset these registers to continue crypto operations. Note that it writes to
 * the registers in the alert manager.
 *
 * @param icache_enabled kHardenedBoolTrue to enable the iCache.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_clear_alerts(void);

/**
 * Initializes the crypto library for use.
 *
 * Check the security configuration
 * Set up alert management
 * Perform (some) KATs for FIPS
 * Set up the entropy source
 *
 * This function writes to alert manager and Ibex registers.
 * It is only usable in M mode.
 *
 * @param security_level Security level of the used key.
 * @returns OK when the security check passed.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_init(otcrypto_key_security_level_t security_level);

/**
 * Function used to return to the user, the last function call of every crypto
 * API. Only to be used when OTCRYPTO_OK can be returned.
 *
 * This function checks whether any alert or sensor was fired.
 *
 * @param security_level Security level of the used key.
 * @returns OK when the security check passed.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_eval_exit(otcrypto_status_t status);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CONFIG_H_
