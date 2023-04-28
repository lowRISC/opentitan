// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_aon_timer.h"

/**
 * Compute the number of AON cycles corresponding to the given microseconds.
 *
 * @param aon_timer An Always-On Timer handle.
 * @param microseconds The number of microseconds.
 * @param[out] cycles The number of AON clock cycles.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aon_timer_testutils_get_aon_cycles_from_us(uint64_t microseconds,
                                                    uint32_t *cycles);

/**
 * Compute the number of microseconds corresponding to the given AON cycles.
 *
 * @param aon_timer An Always-On Timer handle.
 * @param cycles The number of AON clock cycles.
 * @param[out] microseconds The number of microseconds.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aon_timer_testutils_get_us_from_aon_cycles(uint64_t cycles,
                                                    uint32_t *microseconds);

/**
 * Configure wakeup counter for a number of AON clock cycles.
 *
 * @param aon_timer An Always-On Timer handle.
 * @param cycles The number of AON clock cycles.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aon_timer_testutils_wakeup_config(const dif_aon_timer_t *aon_timer,
                                           uint32_t cycles);

/**
 * Configure watchdog counter in number of AON clock cycles.
 *
 * The watchdog counter is set without locking it, and configured so it doesn't
 * pause for low power.
 *
 * @param aon_timer An Always-On Timer handle.
 * @param bark_cycles The number of AON clock cycles till barking.
 * @param bite_cycles The number of AON clock cycles till biting.
 * @param pause_in_sleep Don't increment while sleeping.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aon_timer_testutils_watchdog_config(const dif_aon_timer_t *aon_timer,
                                             uint32_t bark_cycles,
                                             uint32_t bite_cycles,
                                             bool pause_in_sleep);

/**
 * Turn off the AON timer peripheral.
 *
 * At the end of the simulation, stop the wakeup and watchdog timers so that
 * the design stops generating events that may affect the simulation from
 * terminating cleanly. The wakeup and watchdog timer controls are read back
 * to ensure the written value successfully crossed the AON clock domain.
 *
 * @param aon_timer An Always-On Timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aon_timer_testutils_shutdown(const dif_aon_timer_t *aon_timer);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_
