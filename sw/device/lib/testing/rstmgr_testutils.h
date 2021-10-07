// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RSTMGR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RSTMGR_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_rstmgr.h"

/**
 * Determines if the reset_info matches info.
 *
 * @param rstmgr A reset manager handle.
 * @param info A bit mask of reset reasons.
 */
bool rstmgr_testutils_is_reset_info(dif_rstmgr_t *rstmgr,
                                    dif_rstmgr_reset_info_bitfield_t info);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RSTMGR_TESTUTILS_H_
