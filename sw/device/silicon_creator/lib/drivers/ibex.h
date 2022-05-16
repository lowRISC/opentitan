// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Get the FPGA version value from the USR_ACCESS register.
 *
 * @return FPGA version.
 */
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
 * Configure the instruction and data bus in the address translation slot 0.
 *
 * @param matching_addr When an incoming transaction matches the matching
 * region, it is redirected to the new address. If a transaction does not match,
 * then it is directly passed through.
 * @param remap_addr  The region where the matched transtaction will be
 * redirected to.
 * @param size The size of the regions mapped.
 */
void ibex_addr_remap_0_set(uint32_t matching_addr, uint32_t remap_addr,
                           size_t size);

/**
 * Configure the instruction and data bus in the address translation slot 1.
 *
 * @param matching_addr When an incoming transaction matches the matching
 * region, it is redirected to the new address. If a transaction does not match,
 * then it is directly passed through.
 * @param remap_addr  The region where the matched transtaction will be
 * redirected to.
 * @param size The size of the regions mapped.
 */
void ibex_addr_remap_1_set(uint32_t matching_addr, uint32_t remap_addr,
                           size_t size);
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_
