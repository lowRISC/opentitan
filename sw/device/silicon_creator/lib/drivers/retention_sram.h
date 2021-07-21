// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RETENTION_SRAM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RETENTION_SRAM_H_

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Start scrambling the retention SRAM.
 *
 * Requests a new scrambling key for the retention SRAM. This operation
 * will wipe all of the data in the retention SRAM. The retention SRAM
 * will then be initialized to undefined values.
 *
 * The scrambling operation takes time and accesses to retention SRAM
 * will stall until it completes.
 *
 * @returns An error if a new key cannot be requested.
 */
rom_error_t retention_sram_scramble(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RETENTION_SRAM_H_
