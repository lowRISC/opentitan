// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/dt_otp_ctrl.h"  // Generated
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/lib/base/chip.h"

// This is the address that has an ecc error injected.
static volatile const uint32_t kTestAddress = 0;

static dif_otp_ctrl_t otp;

static const dt_otp_ctrl_t kOtpCtrlDt = (dt_otp_ctrl_t)0;
static_assert(kDtOtpCtrlCount >= 1, "This test needs an OTP CTRL");

OTTF_DEFINE_TEST_CONFIG();

static void init_peripherals(void) {
  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  // OTP
  CHECK_DIF_OK(dif_otp_ctrl_init_from_dt(kOtpCtrlDt, &otp));
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));
}

static void check_status(uint32_t expected_code,
                         dif_otp_ctrl_error_t expected_cause) {
  dif_otp_ctrl_status_t status;
  CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp, &status));
  // Clear the non-error status.codes.
  status.codes &= ~((1u << kDifOtpCtrlStatusCodeDaiIdle) |
                    (1u << kDifOtpCtrlStatusCodeCheckPending));
  if (expected_code == 0) {
    CHECK(status.codes == 0,
          "Unexpected OTP status codes, got 0x%x, expected 0", status.codes);
  } else {
    CHECK(status.codes == (1 << expected_code),
          "Unexpected OTP status, got 0x%x, expected 0x%x", status.codes,
          (1 << expected_cause));
    CHECK(status.causes[expected_code] == expected_cause,
          "Unexpected error cause, got 0x%x, expected 0x%x",
          status.causes[expected_code], expected_cause);
  }
}

/**
 * A simple SW test to read from vendor test partition at a location that had
 * an ecc error injected. The expectation is that no error or fault will be
 * triggered. The ecc eror is injected in the associated SV sequence.
 */
bool test_main(void) {
  static const uint32_t kTestPartition = 0;

  init_peripherals();

  uint32_t value;
  LOG_INFO("Testing at OTP address 0x%x", kTestAddress);
  LOG_INFO("Ready for single fault injection");
  busy_spin_micros(1);
  CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32(&otp, kTestPartition,
                                                kTestAddress, &value));
  check_status(0, kDifOtpCtrlErrorOk);
  LOG_INFO("Ready for double fault injection");
  busy_spin_micros(1);
  CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32(&otp, kTestPartition,
                                                kTestAddress, &value));
  check_status(0, kDifOtpCtrlErrorOk);
  LOG_INFO("Address done");
  return true;
}
