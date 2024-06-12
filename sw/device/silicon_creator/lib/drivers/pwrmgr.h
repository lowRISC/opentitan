// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PWRMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PWRMGR_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * The following constants represent the expected number of sec_mmio register
 * writes performed by functions in provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 *
 * Example:
 * ```
 *  pwrmgr_all_resets_enable();
 *  SEC_MMIO_WRITE_INCREMENT(kPwrmgrSecMmioAllResetsEnable);
 * ```
 */
enum {
  kPwrmgrSecMmioAllResetsEnable = 1,
};

/**
 * Synchronize across clock domain.
 *
 * Synchronizes across clock domains by setting the CDC_SYNC register and
 * waiting for it to clear.
 *
 * @param n Number of synchronizations to perform.
 */
void pwrmgr_cdc_sync(uint32_t n);

/**
 * Enable all resets.
 */
void pwrmgr_all_resets_enable(void);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PWRMGR_H_
