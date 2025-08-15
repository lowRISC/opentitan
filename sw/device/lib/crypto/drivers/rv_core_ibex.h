// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/status.h"

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
 * Get random data from the EDN0 interface.
 *
 * Important: this function will hang if the entropy complex is not
 * initialized. Callers are responsible for checking first.
 *
 * @return 32 bits of randomness from EDN0.
 */
uint32_t ibex_rnd32_read(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
