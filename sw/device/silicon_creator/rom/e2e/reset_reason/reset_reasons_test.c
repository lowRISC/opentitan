// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kPor = 1 << kRstmgrReasonPowerOn,
  kSwReset = 1 << kRstmgrReasonSoftwareRequest,
};

bool test_main(void) {
  uint32_t reasons = rstmgr_reason_get();
  LOG_INFO("reset_reasons = %08x", reasons);
  if (reasons == kPor) {
    // If the reasons are only POR, then reset to accumulate reasons and
    // re-enter the test program.
    rstmgr_reset();
  } else if (reasons == (kPor | kSwReset)) {
    // If the reasons are exactly POR|SW, then we're in the second iteration of
    // this test and the ROM did not clear the reset reason (as instructed by
    // OTP).
    return true;
  }
  return false;
}
