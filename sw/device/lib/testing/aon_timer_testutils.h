// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_aon_timer.h"

/**
 * Returns the number of AON cycles corresponding to the given microseconds.
 */
uint32_t aon_timer_testutils_get_aon_cycles_from_us(uint64_t microseconds);

/**
 * Configure wakeup counter for a number of AON clock cycles.
 * @param cycles The number of AON clock cycles.
 */
void aon_timer_testutils_wakeup_config(const dif_aon_timer_t *aon_timer,
                                       uint32_t cycles);

/**
 * Configure watchdog counter in number of AON clock cycles.
 *
 * The watchdog counter is set without locking it, and configured so it doesn't
 * pause for low power.
 * @param bark_cycles The number of AON clock cycles till barking.
 * @param bite_cycles The number of AON clock cycles till biting.
 * @param pause_in_sleep Don't increment while sleeping.
 */
void aon_timer_testutils_watchdog_config(const dif_aon_timer_t *aon_timer,
                                         uint32_t bark_cycles,
                                         uint32_t bite_cycles,
                                         bool pause_in_sleep);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_
