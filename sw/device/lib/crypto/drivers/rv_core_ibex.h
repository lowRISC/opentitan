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
 * Get random data from the EDN0 interface.
 *
 * Important: this function will hang if the entropy complex is not
 * initialized. Callers are responsible for checking first.
 *
 * @return 32 bits of randomness from EDN0.
 */
uint32_t ibex_rnd32_read(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
