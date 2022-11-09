// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_WATCHDOG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_WATCHDOG_H_

#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"

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
 *  watchdog_init(lc);
 *  SEC_MMIO_WRITE_INCREMENT(kWatchdogSecMmioInit);
 * ```
 */
enum {
  kWatchdogSecMmioInit = 4,
  kWatchdogSecMmioConfigure = 4,
  kWatchdogSecMmioDisable = 1,
};

/**
 * Minimum watchdog threshold. Watchdog will not be enabled if the value in the
 * OTP is less than this value.
 */
enum {
  kWatchdogMinThreshold = 1,
};

/**
 * Initialize the watchdog timer.
 *
 * The watchdog bite threshold will be initialized to a value determined by
 * the lifecycle state and OTP configuration.
 *
 * @param lc_state Current lifecycle state.
 */
void watchdog_init(lifecycle_state_t lc_state);

/**
 * Watchdog configuration.
 */
typedef struct watchdog_config {
  /**
   * Bark threshold value in cycles.
   */
  uint32_t bark_threshold;
  /**
   * Bite threshold value in cycles.
   */
  uint32_t bite_threshold;
  /**
   * Whether or not to enable the watchdog timer after it is configured.
   */
  hardened_bool_t enable;
} watchdog_config_t;

/**
 * Configure the watchdog timer with given bite threshold.
 *
 * This operation will set the counter value to 0.
 *
 * @param config Watchdog configuration.
 */
void watchdog_configure(watchdog_config_t config);

/**
 * Disable the watchdog.
 *
 * This will prevent the watchdog from triggering and resetting the chip.
 */
void watchdog_disable(void);

/**
 * Pet the watchdog, thus preventing a watchdog initiated reset.
 */
void watchdog_pet(void);

/**
 * Get the current watchdog counter value.
 *
 * @return current watchdog value.
 */
uint32_t watchdog_get(void);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_WATCHDOG_H_
