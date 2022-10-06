// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_pwrmgr_t pwrmgr;
static dif_pinmux_t pinmux;

// SV randomizes the round of entering/exiting sleep then set this volatile
// variable via backdoor_overwrite.
static volatile const uint8_t kRounds = 2;

// SW testcode randomly chooses the value for 8 GPIO pins (pins are fixed) then
// invert the value for retention. SW will sends the value to SV testbench via
// LOG_INFO().
static const uint8_t kGpioVal = 0x00;

bool test_main(void) {
  bool result = false;

  LOG_INFO("Num Rounds: %3d", kRounds);

  return result;
}
