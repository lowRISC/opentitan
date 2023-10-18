// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BASE_ROM_EPMP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BASE_ROM_EPMP_H_

#include <stdint.h>

#include "sw/lib/sw/device/silicon_creator/epmp_state.h"

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
 * hardware configuration expected at entry to the Base ROM C code.
 *
 * The actual hardware configuration is performed separately, either by reset
 * logic or in assembly. This code must be kept in sync with any changes
 * to the hardware configuration.
 *
 */
void base_rom_epmp_state_init(void);

/**
 * Unlocks the Second ROM region for Read-Execute.
 *
 * The ePMP state is also updated to reflect the changes made to the hardware
 * configuration.
 */
void base_rom_epmp_unlock_second_rom_rx(void);

/**
 * Unlocks the region for the Second ROM patches for Read-Execute.
 *
 * The ePMP state is also updated to reflect the changes made to the hardware
 * configuration.
 *
 * @param region Region covering the patch content to unlock.
 */
void base_rom_epmp_unlock_second_rom_patch_ram(epmp_region_t region);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BASE_ROM_EPMP_H_
