// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otp_ctrl.h"

#include <stdbool.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_otp_ctrl_t otp;

static const char kTestData[] = "abcdefghijklmno";
_Static_assert(ARRAYSIZE(kTestData) % sizeof(uint32_t) == 0,
               "kTestData must be a word array");

const test_config_t kTestConfig;

/**
 * Busy-wait until the DAI is done with whatever operation it is doing.
 */
static void wait_for_dai(void) {
  while (true) {
    dif_otp_ctrl_status_t status;
    CHECK(dif_otp_ctrl_get_status(&otp, &status) == kDifOtpCtrlOk);
    if (bitfield_bit32_read(status.codes, kDifOtpCtrlStatusCodeDaiIdle)) {
      return;
    }
    LOG_INFO("Waiting for DAI...");
  }
}

/**
 * Tests that the OTP can be programed in a particular spot, and that the
 * value can then be read out exactly through the blocking read interface.
 */
bool test_main(void) {
  mmio_region_t otp_reg =
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_BASE_ADDR);
  CHECK(dif_otp_ctrl_init((dif_otp_ctrl_params_t){.base_addr = otp_reg},
                          &otp) == kDifOtpCtrlOk);

  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK(dif_otp_ctrl_configure(&otp, config) == kDifOtpCtrlLockableOk);

  for (int i = 0; i < ARRAYSIZE(kTestData); i += sizeof(uint32_t)) {
    uint32_t word;
    memcpy(&word, &kTestData[i], sizeof(word));

    wait_for_dai();
    dif_otp_ctrl_dai_result_t err = dif_otp_ctrl_dai_program32(
        &otp, kDifOtpCtrlPartitionOwnerSwCfg, 0x100 + i, word);
    CHECK(err == kDifOtpCtrlDaiOk,
          "Failed to program word kTestData[%d] = 0x%8x.", i, word);
  }

  uint32_t readout[ARRAYSIZE(kTestData) / sizeof(uint32_t)] = {0};
  dif_otp_ctrl_dai_result_t err =
      dif_otp_ctrl_read_blocking(&otp, kDifOtpCtrlPartitionOwnerSwCfg, 0x100,
                                 readout, ARRAYSIZE(kTestData));
  CHECK(err == kDifOtpCtrlDaiOk, "Failed to perform OTP blocking readout.");

  CHECK(memcmp(kTestData, readout, ARRAYSIZE(kTestData)) == 0);

  return true;
}
