// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_

#include "sw/device/lib/dif/dif_otp_ctrl.h"

/**
 * Enum that encodes the expectation for the check_dai_access_error function.
 */
typedef enum { kExpectPassed, kExpectFailed } exp_test_result_t;

/**
 * Check whether we got an access error in the DAI.
 *
 * The test passes depending on the expectation argument.
 * I.e., if the expectation is that we get an access error (exp_result ==
 * kExpectFailed), but the DAI does not report any error, the test will fail.
 */
void otp_ctrl_testutils_dai_access_error_check(const dif_otp_ctrl_t *otp_ctrl,
                                               exp_test_result_t exp_result,
                                               int32_t address);

/**
 * Waits for the DAI operation to finish (busy wait).
 */
void otp_ctrl_testutils_wait_for_dai(const dif_otp_ctrl_t *otp_ctrl);

/**
 * Issues a partition lock and waits for the DAI operation to finish (busy
 * wait).
 */
void otp_ctrl_testutils_lock_partition(const dif_otp_ctrl_t *otp,
                                       dif_otp_ctrl_partition_t partition,
                                       uint64_t digest);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_
