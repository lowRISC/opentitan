// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/silicon_creator/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Get the FPGA version value from the USR_ACCESS register.
 *
 * @return FPGA version.
 */
OT_WARN_UNUSED_RESULT
uint32_t ibex_fpga_version(void);

/**
 * The following constants represent the expected number of sec_mmio register
 * writes performed by functions in provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 *
 * Example:
 * ```
 *  ibex_addr_remap_0_set(...);
 *  SEC_MMIO_WRITE_INCREMENT(kAddressTranslationSecMmioConfigure);
 * ```
 */
enum {
  kAddressTranslationSecMmioConfigure = 6,
};

/**
 * Get the number of address remapper slots.
 *
 * @return Number of remapper slots.
 */
OT_WARN_UNUSED_RESULT
unsigned ibex_addr_remap_slots(void);

/**
 * Configure the instruction and data bus in an address translation slot.
 *
 * @param slot Index of the address translation slot to configure.
 * @param matching_addr When an incoming transaction matches the matching
 * region, it is redirected to the new address. If a transaction does not match,
 * then it is directly passed through.
 * @param remap_addr  The region where the matched transtaction will be
 * redirected to.
 * @param size The size of the regions mapped.
 */
OT_WARN_UNUSED_RESULT
rom_error_t ibex_addr_remap_set(size_t slot, uint32_t matching_addr,
                                uint32_t remap_addr, size_t size);

/**
 * Lock an address translation slot for the instruction and data bus.
 *
 * @param slot Index of the address translation slot to lock.
 */
OT_WARN_UNUSED_RESULT
rom_error_t ibex_addr_remap_lock(size_t slot);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_
