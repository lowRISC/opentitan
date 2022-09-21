// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_EPMP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_EPMP_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * ROM enhanced Physical Memory Protection (ePMP) library.
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

/**
 * Initialise the ePMP in-memory copy of the register state to reflect the
 * hardware configuration expected at entry to the ROM C code.
 *
 * The actual hardware configuration is performed separately, either by reset
 * logic or in assembly. This code must be kept in sync with any changes
 * to the hardware configuration.
 *
 * @param lc_state The current lifecycle state to check for debug enable.
 */
void rom_epmp_state_init(lifecycle_state_t lc_state);

/**
 * Unlocks the provided ROM_EXT image region with read-execute permissions.
 *
 * The provided ePMP state is also updated to reflect the changes made to the
 * hardware configuration.
 *
 * @param region Region for executable sections in ROM_EXT image.
 */
void rom_epmp_unlock_rom_ext_rx(epmp_region_t region);

/**
 * Unlocks the provided ROM_EXT image region with read-only permissions.
 *
 * The provided ePMP state is also updated to reflect the changes made to the
 * hardware configuration.
 * The image size must be power of 2 as this function uses NAPOT
 * (Naturally-Aligned-Power-Of-Two) addressing mode.
 *
 * @param region Region in the ROM_EXT image to receive read-only permission.
 */
void rom_epmp_unlock_rom_ext_r(epmp_region_t region);
/**
 * Configure the ePMP entry to manage access to Debug ROM based on life cycle
 * state.
 *
 * @param lc_state The current lifecycle state to check for debug enable.
 */
void rom_epmp_config_debug_rom(lifecycle_state_t lc_state);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_EPMP_H_
