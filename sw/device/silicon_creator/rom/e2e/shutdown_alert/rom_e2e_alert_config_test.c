// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/alert.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Check that the alert_handler register CRC32 matches OTP value.
 *
 * The `OWNER_SW_CFG_ROM_ALERT_DIGEST_<LC_STATE>` OTP word should match the
 * digest computed by XORing the CRC32 of the alert_handler registers with the
 * current lifecycle state and kErrorOk, as done in
 * `sw/device/silicon_creator/lib/shutdown.c:shutdown_init`.
 */
static void alert_cfg_test(void) {
  uint32_t digest = alert_config_crc32() ^ lifecycle_state_get() ^ kErrorOk;

  // `OTP_ALERT_DIGEST` in configured for each test to reference the digest for
  // the current LC state.
  CHECK(digest == otp_read32(OTP_ALERT_DIGEST));
}

bool test_main(void) {
  alert_cfg_test();
  return true;
}
