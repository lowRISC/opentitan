// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_EPMP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_EPMP_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/epmp_state.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enhanced Physical Memory Protection (ePMP) library.
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
 * Clear an ePMP entry.
 *
 * Sets the PMPADDR and PMPCFG entries to zero.
 *
 * @param entry The ePMP entry to clear.
 */
void epmp_clear(uint8_t entry);

/**
 * Configures an ePMP entry for a NAPOT or NA4 region.
 *
 * The region start must have an alignment consistend with the region size.  The
 * region size must be a power of two.  If either of these conditions is not
 * met, this function will fault.
 *
 * From a configuration perspective, an NA4 region is just a special case of a
 * NAPOT region.
 *
 * @param entry The ePMP entry to configure.
 * @param region The address region to configure.
 * @param perm The ePMP permissions for the region.
 */
void epmp_set_napot(uint8_t entry, epmp_region_t region, epmp_perm_t perm);

/**
 * Configures an ePMP entry for a TOR region.
 *
 * The region start and end may be abitrary addresses.  The start will be
 * rounded down to a 4-byte address.  The end will be rounded up to a 4-byte
 * address.
 *
 * @param entry The ePMP entry to configure.
 * @param region The address region to configure.
 * @param perm The ePMP permissions for the region.
 */
void epmp_set_tor(uint8_t entry, epmp_region_t region, epmp_perm_t perm);

/**
 * Clear the rule-locking-bypass (RLB) bit.
 *
 * Clearing RLB causes the Lock bit in the ePMP to be enforced.
 */
void epmp_clear_rlb(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_EPMP_H_
