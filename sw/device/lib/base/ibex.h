// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_IBEX_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"

/**
 * Wait for random data in the RND_DATA CSR to be valid.
 *
 * Important: this function will hang if the entropy complex is not
 * initialized. Callers are responsible for checking first.
 *
 * Returns once the random data is valid.
 */
void ibex_wait_rnd_valid(void);

/**
 * Get random data from the EDN0 interface.
 *
 * Important: this function will hang if the entropy complex is not
 * initialized. Callers are responsible for checking first.
 *
 * @return 32 bits of randomness from EDN0.
 */
uint32_t ibex_rnd_data_read(void);

/**
 * Get information on the state of the RND_DATA CSR.
 *
 * @return the status of the randomness interface.
 */
uint32_t ibex_rnd_status_read(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_IBEX_H_
