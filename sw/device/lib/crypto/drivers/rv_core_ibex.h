// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/impl/status.h"

/**
 * Disable the Ibex Instruction Cache if it is enabled.
 *
 * Reads out the current state of the instruction cache. If it is enabled,
 * disable it for the crypto lib.
 *
 * @param[out] icache_enabled kHardenedBoolTrue if the iCache was enabled before
 * we disabled it.
 * @return Error status.
 */
status_t ibex_disable_icache(hardened_bool_t *icache_enabled);

/**
 * Enables the Ibex Instruction Cache if icache_enabled is set.
 *
 * If icache_enabled == kHardenedBoolTrue, this function enables the iCache by
 * writing to CPUCTRL.
 */
void ibex_restore_icache(hardened_bool_t icache_enabled);

/**
 * Checks if the expected Ibex Security Features are enabled.
 *
 * This function reads Ibex cpuctrl register and checks, whether the following
 * security features are enabled:
 * - data_ind_timing
 * - dummy_instr_en
 *
 * @returns Whether the config matches the expected secure config.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t ibex_check_security_config(void);

/**
 * Write a random value into x5...x7 and x9...x31.
 *
 * To avoid having SCA sensitive variables in the register file, this function
 * overwrites the RF with a random value.
 * Important:
 * - This function does not overwrite x8/x9 as this might not work with all
 *   compilers. For more information see llvm/llvm-project#157694.
 *   However, ibex_clear_rf() makes sure that x8/x9 is not used for secret
 *   data.
 * - This function will hang if the entropy complex is not initialized.
 *   Callers are responsible for checking first.
 */
void ibex_clear_rf(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
