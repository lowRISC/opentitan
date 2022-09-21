// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_EPMP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_EPMP_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/epmp_state.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * ROM_EXT ROM enhanced Physical Memory Protection (ePMP) library.
 *
 * The ePMP configuration is managed in two parts:
 *
 *   1. The actual hardware configuration held in CSRs
 *   2. The in-memory copy of register values in `epmp_state_t` that is used
 *      to verify the CSRs
 *
 * Every time the hardware configuration is updated the in-memory copy
 * must also be updated. The hardware configuration is usually interacted
 * with directly using the CSR library or assembly whereas the in-memory
 * copy of the state should normally be modified using configuration functions
 * from the silicon creator ePMP library.
 *
 * This separation of concerns allows the hardware configuration to be
 * updated efficiently as needed (including before the C runtime is
 * initialized) with the in-memory copy of the state used to double check the
 * configuration as required.
 */
// TODO(lowrisc/opentitan#8800): Implement ePMP initialization for ROM_EXT
// stage.

/**
 * Unlocks the provided first Silicon Owner stage region with read-execute
 * permissions.
 *
 * The provided ePMP state is also updated to reflect the changes made to the
 * hardware configuration.
 *
 * @param state The ePMP state to update.
 * @param image Region for executable sections in the silicon Owner image.
 */
void rom_ext_epmp_unlock_owner_stage_rx(epmp_region_t image);

/**
 * Unlocks the provided first silicon owner region with read-only permissions.
 *
 * The provided ePMP state is also updated to reflect the changes made to the
 * hardware configuration.
 * The image size must be a power of 2 as this function uses NAPOT
 * (Naturally-Aligned-Power-Of-Two) addressing mode.
 *
 * @param state The ePMP state to update.
 * @param region Region in the silicon Owner image to receive read-only
 * permission.
 */
void rom_ext_epmp_unlock_owner_stage_r(epmp_region_t region);
#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_EPMP_H_
