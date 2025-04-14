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
 * Returns OTCRYPTO_OK when the random data is valid.
 *
 * @return OTCRYPTO_OK.
 */
status_t ibex_wait_rnd_valid(void);

/**
 * Get random data from the EDN0 interface.
 *
 * Returns 32 bits of randomness from EDN0.
 *
 * @param rnd_data The random data pointer.
 * @return OTCRYPTO_OK.
 */
status_t ibex_rnd_data_read(uint32_t *rnd_data);

/**
 * Get information on the state of the RND_DATA CSR.
 *
 * Returns the status of the randomness interface.
 *
 * @param rnd_status The status pointer.
 * @return OTCRYPTO_OK.
 */
status_t ibex_rnd_status_read(uint32_t *rnd_status);

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_IBEX_H_
