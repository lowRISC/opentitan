// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_

#include "sw/device/lib/dif/dif_otp_ctrl.h"

/**
 * Waits for the DAI operation to finish (busy wait).
 */
void otp_ctrl_testutils_wait_for_dai(const dif_otp_ctrl_t *otp_ctrl);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_
