// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define LC_TOKEN_SIZE 16

static dif_lc_ctrl_t lc;
static dif_otp_ctrl_t otp;

/**
 * Track LC state transition tokens.
 *
 * These tokens will be further randomized and overridden by the testbench.
 */

// LC exit token value for LC state transition.
static volatile const uint8_t kLcExitToken[LC_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

// LC exit token value in OTP secret0 partition.
static volatile const uint8_t kOtpExitToken[LC_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

// LC unlock token value in OTP secret0 partition.
static volatile const uint8_t kOtpUnlockToken[LC_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

static void check_lc_state_transition_count(uint8_t exp_lc_count) {
  LOG_INFO("Read LC count and check with expect_val=%0d", exp_lc_count);
  uint8_t lc_count;
  CHECK_DIF_OK(dif_lc_ctrl_get_attempts(&lc, &lc_count),
               "Read lc_count register failed!");
  CHECK(lc_count == exp_lc_count,
        "LC_count error, expected %0d but actual count is %0d", exp_lc_count,
        lc_count);
}

/**
 * Walkthrough LC state: RAW -> TestUnlock0 -> ProdEnd.
 *
 * 1). Preload OTP RAW image file.
 * 2). DV sequence drives JTAG interface to write RawUnlockToken and
 * transfers LC state to TestUnlock0 state.
 * 3). In TestUnlock0 state, SW programs OTP secret0 partition to write
 * ExitToken and TestUnlockToken.
 * 4). DV sequence issues reset to lock OTP secret0 partition.
 * 5). SW requests a LC state transfer to ProdEnd state with the correct
 * TestLockToken.
 * 6). DV sequence issues reset and SW check if LC transfers to ProdEnd state.
 */

bool test_main(void) {
  LOG_INFO("Start LC walkthrough ProdEnd test.");

  mmio_region_t lc_reg = mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc));

  mmio_region_t otp_reg =
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(otp_reg, &otp));

  LOG_INFO("Read and check LC state and count.");
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));

  if (curr_state == kDifLcCtrlStateTestUnlocked0) {
    check_lc_state_transition_count(1);
    bool secret0_locked;
    CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
        &otp, kDifOtpCtrlPartitionSecret0, &secret0_locked));

    if (secret0_locked == false) {
      // Write LC tokens to OTP secret0 partition.
      uint64_t otp_unlock_token_0 = 0;
      uint64_t otp_unlock_token_1 = 0;
      for (int i = 0; i < LC_TOKEN_SIZE; i++) {
        if (i < LC_TOKEN_SIZE / 2) {
          otp_unlock_token_0 =
              otp_unlock_token_0 | ((uint64_t)kOtpUnlockToken[i] << (i * 8));
        } else {
          otp_unlock_token_1 =
              otp_unlock_token_1 |
              ((uint64_t)kOtpUnlockToken[i] << ((i - LC_TOKEN_SIZE / 2) * 8));
        }
      }

      uint64_t otp_exit_token_0 = 0;
      uint64_t otp_exit_token_1 = 0;
      for (int i = 0; i < LC_TOKEN_SIZE; i++) {
        if (i < LC_TOKEN_SIZE / 2) {
          otp_exit_token_0 =
              otp_exit_token_0 | ((uint64_t)kOtpExitToken[i] << (i * 8));
        } else {
          otp_exit_token_1 =
              otp_exit_token_1 |
              ((uint64_t)kOtpExitToken[i] << ((i - LC_TOKEN_SIZE / 2) * 8));
        }
      }

      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret0,
                                              /*address=*/0x0,
                                              /*value=*/otp_unlock_token_0));
      otp_ctrl_testutils_wait_for_dai(&otp);

      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret0,
                                              /*address=*/0x8,
                                              /*value=*/otp_unlock_token_1));
      otp_ctrl_testutils_wait_for_dai(&otp);

      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret0,
                                              /*address=*/0x10,
                                              /*value=*/otp_exit_token_0));
      otp_ctrl_testutils_wait_for_dai(&otp);

      CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret0,
                                              /*address=*/0x18,
                                              /*value=*/otp_exit_token_1));
      otp_ctrl_testutils_wait_for_dai(&otp);

      CHECK_DIF_OK(dif_otp_ctrl_dai_digest(&otp, kDifOtpCtrlPartitionSecret0,
                                           /*digest=*/0));
      otp_ctrl_testutils_wait_for_dai(&otp);

      LOG_INFO("Written and locked OTP secret0 partition!");
      return true;
    } else {
      // Issue a LC state transfer to ProdEnd state.
      dif_lc_ctrl_token_t token;
      for (int i = 0; i < LC_TOKEN_SIZE; i++) {
        token.data[i] = kLcExitToken[i];
      }
      CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc));
      dif_lc_ctrl_settings_t settings;
      // TODO: randomize using external or internal clock.
      settings.clock_select = kDifLcCtrlExternalClockEn;
      CHECK_DIF_OK(dif_lc_ctrl_transition(&lc, kDifLcCtrlStateProdEnd, &token,
                                          &settings),
                   "LC_transition failed!");

      LOG_INFO("Waiting for LC transtition done and reboot.");
      return true;
    }
  } else {
    // Check LC enters ProdEnd state.
    CHECK(curr_state == kDifLcCtrlStateProdEnd);
    check_lc_state_transition_count(2);
    return true;
  }
}
