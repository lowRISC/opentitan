// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/otp_ctrl_testutils.h"

#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"

/*
 * OTP the Direct Access Interface (DAI) operation time-out in micro seconds.
 *
 * It is not possible to predict the specific cycle count that a DAI operation
 * takes, thus arbitrary value of 100us is used.
 */
const uint8_t kOtpDaiTimeoutUs = 100;

/**
 * Checks whether the DAI operation has finished.
 */
static bool dai_finished(const dif_otp_ctrl_t *otp_ctrl) {
  dif_otp_ctrl_status_t status;
  CHECK_DIF_OK(dif_otp_ctrl_get_status(otp_ctrl, &status));
  return bitfield_bit32_read(status.codes, kDifOtpCtrlStatusCodeDaiIdle);
}

void otp_ctrl_testutils_wait_for_dai(const dif_otp_ctrl_t *otp_ctrl) {
  IBEX_SPIN_FOR(dai_finished(otp_ctrl), kOtpDaiTimeoutUs);
}
