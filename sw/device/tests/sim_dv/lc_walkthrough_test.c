// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define LC_TOKEN_SIZE 16

OTTF_DEFINE_TEST_CONFIG();

static dif_lc_ctrl_t lc;
static dif_otp_ctrl_t otp;
static dif_rstmgr_t rstmgr;

/**
 * Track LC state transition tokens and destination state.
 *
 * These variables will be further randomized and overridden by the testbench.
 */

static volatile const uint8_t kDestState;

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

// LC rma token value for LC state transition.
static volatile const uint8_t kLcRmaToken[LC_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

// LC rma token value in OTP secret2 partition.
static volatile const uint8_t kOtpRmaToken[LC_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

static void lock_otp_secret0_partition(void) {
  uint64_t otp_unlock_token_0 = 0;
  uint64_t otp_unlock_token_1 = 0;
  for (int i = 0; i < LC_TOKEN_SIZE; i++) {
    if (i < LC_TOKEN_SIZE / 2) {
      otp_unlock_token_0 |= (uint64_t)kOtpUnlockToken[i] << (i * 8);
    } else {
      otp_unlock_token_1 |= (uint64_t)kOtpUnlockToken[i]
                            << ((i - LC_TOKEN_SIZE / 2) * 8);
    }
  }

  uint64_t otp_exit_token_0 = 0;
  uint64_t otp_exit_token_1 = 0;
  for (int i = 0; i < LC_TOKEN_SIZE; i++) {
    if (i < LC_TOKEN_SIZE / 2) {
      otp_exit_token_0 |= (uint64_t)kOtpExitToken[i] << (i * 8);
    } else {
      otp_exit_token_1 |= (uint64_t)kOtpExitToken[i]
                          << ((i - LC_TOKEN_SIZE / 2) * 8);
    }
  }

  CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret0,
                                          /*address=*/0x0,
                                          /*value=*/otp_unlock_token_0));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
  CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret0,
                                          /*address=*/0x8,
                                          /*value=*/otp_unlock_token_1));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
  CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret0,
                                          /*address=*/0x10,
                                          /*value=*/otp_exit_token_0));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
  CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret0,
                                          /*address=*/0x18,
                                          /*value=*/otp_exit_token_1));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));

  CHECK_DIF_OK(dif_otp_ctrl_dai_digest(&otp, kDifOtpCtrlPartitionSecret0,
                                       /*digest=*/0));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
}

static void lock_otp_secret2_partition(void) {
  // Write LC RMA tokens to OTP secret2 partition.
  uint64_t otp_rma_token_0 = 0;
  uint64_t otp_rma_token_1 = 0;
  for (int i = 0; i < LC_TOKEN_SIZE; i++) {
    if (i < LC_TOKEN_SIZE / 2) {
      otp_rma_token_0 |= (uint64_t)kOtpRmaToken[i] << (i * 8);
    } else {
      otp_rma_token_1 |= (uint64_t)kOtpRmaToken[i]
                         << ((i - LC_TOKEN_SIZE / 2) * 8);
    }
  }
  CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret2,
                                          /*address=*/0x0,
                                          /*value=*/otp_rma_token_0));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
  CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret2,
                                          /*address=*/0x8,
                                          /*value=*/otp_rma_token_1));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));

  CHECK_DIF_OK(dif_otp_ctrl_dai_digest(&otp, kDifOtpCtrlPartitionSecret2,
                                       /*digest=*/0));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
}

/**
 * Walkthrough LC state: RAW -> TestUnlock0 -> Destination -> RMA (if
 * applicable).
 *
 * 1). Preload OTP RAW image file.
 * 2). DV sequence drives JTAG interface to write RawUnlockToken and
 * transfers LC state to TestUnlock0 state.
 * 3). In TestUnlock0 state, SW programs OTP secret0 partition to write
 * ExitToken and TestUnlockToken.
 * Also programs OTP secret2 partition to write RmaToken.
 * 4). DV sequence issues reset to lock OTP secret0 partition.
 * 5). SW requests a LC state transfer to ProdEnd state with the correct
 * TestLockToken.
 * 6). DV sequence issues reset and SW check if LC transfers to the destination
 * state.
 * 7). If the destination state can be transferred to RMA state, will issue
 * another LC state transfer to RMA state.
 *
 * Note that the destination state is a runtime input from the testbench.
 */

bool test_main(void) {
  LOG_INFO("Start LC walkthrough %d test.", kDestState);

  mmio_region_t lc_reg = mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc));

  mmio_region_t otp_reg =
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(otp_reg, &otp));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  LOG_INFO("Read and check LC state and count.");
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));

  if (curr_state == kDifLcCtrlStateTestUnlocked0) {
    CHECK_STATUS_OK(lc_ctrl_testutils_check_transition_count(&lc, 1));
    bool secret0_locked;
    CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
        &otp, kDifOtpCtrlPartitionSecret0, &secret0_locked));

    if (!secret0_locked) {
      LOG_INFO("In TestUnlocked0 state. Write and lock OTP secret0 partition.");
      lock_otp_secret0_partition();
      LOG_INFO("Written and locked OTP secret0 partition!");
      CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
      wait_for_interrupt();
      // Print out LcRmaToken to avoid SW compile error saying kLcRmaToken is
      // unused in certain state trasition tests.
      LOG_INFO("LC RMA token start with %08x", kLcRmaToken[0]);
      // Unreachable
      return false;
    } else {
      LOG_INFO(
          "In TestUnlocked0 state. Issue LC state transfer to destination "
          "state.");
      dif_lc_ctrl_token_t token;
      for (int i = 0; i < LC_TOKEN_SIZE; i++) {
        if (kDestState != kDifLcCtrlStateRma) {
          token.data[i] = kLcExitToken[i];
        } else {
          // Transition from TestUnlock to Rma state is unconditional and
          // requires to write all zero default tokens.
          token.data[i] = 0;
        }
      }

      CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc));

      // TODO(lowRISC/opentitan#12775): randomize using external or internal
      // clock.
      bool use_ext_clock = false;
      CHECK_DIF_OK(
          dif_lc_ctrl_configure(&lc, kDestState, use_ext_clock, &token),
          "LC transition configuration failed!");
      CHECK_DIF_OK(dif_lc_ctrl_transition(&lc), "LC transition failed!");

      LOG_INFO("Waiting for LC transition done and reboot.");
      wait_for_interrupt();

      // Unreachable.
      return false;
    }
  } else if (curr_state == kDestState) {
    bool secret2_locked;
    CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
        &otp, kDifOtpCtrlPartitionSecret2, &secret2_locked));

    if (!secret2_locked) {
      LOG_INFO(
          "In destination state. Check LC count and lock secret2 partition.");
      CHECK(curr_state == kDestState);
      CHECK_STATUS_OK(lc_ctrl_testutils_check_transition_count(&lc, 2));

      lock_otp_secret2_partition();
      LOG_INFO("Written and locked OTP secret2 partition in next power cycle!");
      CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
      wait_for_interrupt();
      return false;

    } else {
      if (kDestState == kDifLcCtrlStateRma ||
          kDestState == kDifLcCtrlStateProdEnd) {
        CHECK_STATUS_OK(lc_ctrl_testutils_check_transition_count(&lc, 2));
        LOG_INFO("LC transition done!");
        return true;
      } else {
        // Check LC counts and transit to RMA state.
        LOG_INFO(
            "In destination state. Check LC count and transfer to RMA "
            "state.");
        CHECK_STATUS_OK(lc_ctrl_testutils_check_transition_count(&lc, 2));

        // Issue a LC state transfer to destination state.
        dif_lc_ctrl_token_t token;
        for (int i = 0; i < LC_TOKEN_SIZE; i++) {
          token.data[i] = kLcRmaToken[i];
        }

        CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc));

        // TODO: randomize using external or internal clock.
        bool use_ext_clock = true;
        CHECK_DIF_OK(dif_lc_ctrl_configure(&lc, kDifLcCtrlStateRma,
                                           use_ext_clock, &token),
                     "LC transition configuration failed!");
        CHECK_DIF_OK(dif_lc_ctrl_transition(&lc), "LC transition failed!");

        LOG_INFO("Waiting for LC RMA transition done and reboot.");
        wait_for_interrupt();

        // Unreachable.
        return false;
      }
    }
  } else {
    LOG_INFO("In RMA state. Check LC count and exit.");
    CHECK(curr_state == kDifLcCtrlStateRma);
    CHECK_STATUS_OK(lc_ctrl_testutils_check_transition_count(&lc, 3));
    return true;
  }
}
