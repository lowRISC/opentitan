// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_

#include <stddef.h>
#include <stdint.h>

/**
 * Get random data from the EDN0 interface.
 *
 * Important: this function will hang if the entropy complex is not
 * initialized. Callers are responsible for checking first.
 *
 * @return 32 bits of randomness from EDN0.
 */
uint32_t ibex_rnd32_read(void);

/**
 * Write a random value into x5...x7, x9...x31.
 *
 * To avoid having SCA sensitive variables in the register file, this function
 * overwrites the RF with a random value.
 * Important: this function will hang if the entropy complex is not
 * initialized. Callers are responsible for checking first.
 */
void ibex_clear_rf(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
