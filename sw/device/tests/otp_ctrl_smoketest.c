// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_otp_ctrl_t otp;

static const char kTestData[] = "abcdefghijklmno";
static_assert(ARRAYSIZE(kTestData) % sizeof(uint32_t) == 0,
              "kTestData must be a word array");

OTTF_DEFINE_TEST_CONFIG();

/**
 * Tests that the OTP can be programed in a particular spot, and that the
 * value can then be read out exactly through the blocking read interface.
 */
bool test_main(void) {
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));

  for (uint32_t i = 0; i < ARRAYSIZE(kTestData); i += sizeof(uint32_t)) {
    uint32_t word;
    memcpy(&word, &kTestData[i], sizeof(word));

    CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
    CHECK_DIF_OK(dif_otp_ctrl_dai_program32(
                     &otp, kDifOtpCtrlPartitionVendorTest, 0x10 + i, word),
                 "Failed to program word kTestData[%d] = 0x%08x.", i, word);
  }

  uint32_t readout[ARRAYSIZE(kTestData) / sizeof(uint32_t)] = {0};
  CHECK_DIF_OK(dif_otp_ctrl_read_blocking(&otp, kDifOtpCtrlPartitionVendorTest,
                                          0x10, readout, ARRAYSIZE(kTestData)),
               "Failed to perform OTP blocking readout.");

  CHECK(memcmp(kTestData, readout, ARRAYSIZE(kTestData)) == 0);

  return true;
}
