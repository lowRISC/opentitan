// Copyright lowRISC contributors (OpenTitan project).
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
 * Track LC state transition tokens.
 *
 * These tokens will be further randomized and overridden by the testbench.
 */

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

static void get_dest_state_and_cnt(dif_lc_ctrl_state_t *curr_state,
                                   dif_lc_ctrl_state_t *dest_state,
                                   uint8_t *exp_cnt) {
  switch (*curr_state) {
    case kDifLcCtrlStateTestUnlocked0:
      *dest_state = kDifLcCtrlStateTestLocked0;
      *exp_cnt = 1;
      break;
    case kDifLcCtrlStateTestUnlocked1:
      *dest_state = kDifLcCtrlStateTestLocked1;
      *exp_cnt = 3;
      break;
    case kDifLcCtrlStateTestUnlocked2:
      *dest_state = kDifLcCtrlStateTestLocked2;
      *exp_cnt = 5;
      break;
    case kDifLcCtrlStateTestUnlocked3:
      *dest_state = kDifLcCtrlStateTestLocked3;
      *exp_cnt = 7;
      break;
    case kDifLcCtrlStateTestUnlocked4:
      *dest_state = kDifLcCtrlStateTestLocked4;
      *exp_cnt = 9;
      break;
    case kDifLcCtrlStateTestUnlocked5:
      *dest_state = kDifLcCtrlStateTestLocked5;
      *exp_cnt = 11;
      break;
    case kDifLcCtrlStateTestUnlocked6:
      *dest_state = kDifLcCtrlStateTestLocked6;
      *exp_cnt = 13;
      break;
    case kDifLcCtrlStateTestUnlocked7:
      *dest_state = kDifLcCtrlStateRaw;
      *exp_cnt = 15;
      break;
    default:
      LOG_FATAL("Unexpected state = %d", curr_state);
      abort();
  }
}

/**
 * Walkthrough LC all TestUnlock and TestLock states.
 *
 * 1). Preload OTP RAW image file.
 * 2). DV sequence drives JTAG interface to write RawUnlockToken and
 * transfers LC state to TestUnlock0 state.
 * 3). In TestUnlock0 state, SW programs OTP secret0 partition to write
 * ExitToken and TestUnlockToken.
 * 4). DV sequence issues reset to lock OTP secret0 partition.
 * 5). SW requests a LC state transfer to TestLock0 state with all zero tokens.
 * 6). DV sequence issues reset and SW check if LC transfers to the destination
 * state.
 * 7). DV sequence requests a LC state transfer to TestUnlock1 state with test
 * unlock tokens.
 * Repeat the above transition until reaches the last TestUnlock state.
 *
 */

bool test_main(void) {
  LOG_INFO("Start LC walkthrough testunlocks test.");

  mmio_region_t lc_reg =
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc));

  mmio_region_t otp_reg =
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(otp_reg, &otp));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  LOG_INFO("Read and check LC state and count.");
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));

  dif_lc_ctrl_state_t kDestState;
  uint8_t kExpCnt;
  get_dest_state_and_cnt(&curr_state, &kDestState, &kExpCnt);

  CHECK_STATUS_OK(lc_ctrl_testutils_check_transition_count(&lc, kExpCnt));

  bool secret0_locked;
  CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
      &otp, kDifOtpCtrlPartitionSecret0, &secret0_locked));
  if (!secret0_locked) {
    // Write LC tokens to OTP secret0 partition.
    lock_otp_secret0_partition();
    LOG_INFO("Wrote and locked OTP secret0 partition!");
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    wait_for_interrupt();
    // Unreachable
    return false;
  }

  if (kDestState != kDifLcCtrlStateRaw) {
    // Issue a LC state transfer to destination state.
    dif_lc_ctrl_token_t token;
    for (int i = 0; i < LC_TOKEN_SIZE; i++) {
      // Transition from TestUnlock to TestLock state is unconditional and
      // requires to write all zero default tokens.
      token.data[i] = 0;
    }

    CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc));

    // TODO(lowRISC/opentitan#12775): randomize using external or internal
    // clock.
    bool use_ext_clock = false;
    CHECK_DIF_OK(dif_lc_ctrl_configure(&lc, kDestState, use_ext_clock, &token),
                 "LC transition configuration failed!");
    CHECK_DIF_OK(dif_lc_ctrl_transition(&lc), "LC transition failed!");

    LOG_INFO("Waiting for LC transtition %d done and reboot.", kDestState);
    wait_for_interrupt();

    // Unreachable.
    return false;
  } else {
    // Reached TestUnlock7 state, exit SW test.
    return true;
  }
}
