// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_aon_timer.h"

/**
 * Set an aon timer for a number of AON clock cycles.
 * @param cycles The number of AON clock cycles.
 */
void aon_timer_testutils_wakeup_config(dif_aon_timer_t *aon_timer,
                                       uint32_t cycles);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_AON_TIMER_TESTUTILS_H_
