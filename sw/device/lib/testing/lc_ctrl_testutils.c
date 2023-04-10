// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/lc_ctrl_testutils.h"

#include <stdbool.h>

#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

status_t lc_ctrl_testutils_lc_state_log(const dif_lc_ctrl_state_t *state) {
  switch (*state) {
    case kDifLcCtrlStateTestUnlocked0:
      LOG_INFO("Life cycle state: TEST_UNLOCKED0");
      break;
    case kDifLcCtrlStateTestUnlocked1:
      LOG_INFO("Life cycle state: TEST_UNLOCKED1");
      break;
    case kDifLcCtrlStateTestUnlocked2:
      LOG_INFO("Life cycle state: TEST_UNLOCKED2");
      break;
    case kDifLcCtrlStateTestUnlocked3:
      LOG_INFO("Life cycle state: TEST_UNLOCKED3");
      break;
    case kDifLcCtrlStateTestUnlocked4:
      LOG_INFO("Life cycle state: TEST_UNLOCKED4");
      break;
    case kDifLcCtrlStateTestUnlocked5:
      LOG_INFO("Life cycle state: TEST_UNLOCKED5");
      break;
    case kDifLcCtrlStateTestUnlocked6:
      LOG_INFO("Life cycle state: TEST_UNLOCKED6");
      break;
    case kDifLcCtrlStateTestUnlocked7:
      LOG_INFO("Life cycle state: TEST_UNLOCKED7");
      break;
    case kDifLcCtrlStateDev:
      LOG_INFO("Life cycle state: DEV");
      break;
    case kDifLcCtrlStateProd:
      LOG_INFO("Life cycle state: PROD");
      break;
    case kDifLcCtrlStateProdEnd:
      LOG_INFO("Life cycle state: PROD_END");
      break;
    case kDifLcCtrlStateRma:
      LOG_INFO("Life cycle state: RMA");
      break;
    default:
      LOG_ERROR("CPU is executing in locked/invalid life cycle state: %d",
                (uint32_t)state);
      return FAILED_PRECONDITION();
  }
  return OK_STATUS();
}

status_t lc_ctrl_testutils_debug_func_enabled(const dif_lc_ctrl_t *lc_ctrl,
                                              bool *debug_enabled) {
  dif_lc_ctrl_state_t state;
  TRY(dif_lc_ctrl_get_state(lc_ctrl, &state));

  switch (state) {
    case kDifLcCtrlStateTestUnlocked0:
    case kDifLcCtrlStateTestUnlocked1:
    case kDifLcCtrlStateTestUnlocked2:
    case kDifLcCtrlStateTestUnlocked3:
    case kDifLcCtrlStateTestUnlocked4:
    case kDifLcCtrlStateTestUnlocked5:
    case kDifLcCtrlStateTestUnlocked6:
    case kDifLcCtrlStateTestUnlocked7:
    case kDifLcCtrlStateDev:
    case kDifLcCtrlStateRma:
      *debug_enabled = true;
      break;
    default:
      *debug_enabled = false;
      break;
  }
  return OK_STATUS();
}

status_t lc_ctrl_testutils_check_transition_count(const dif_lc_ctrl_t *lc_ctrl,
                                                  uint8_t exp_lc_count) {
  LOG_INFO("Read LC count and check with expect_val=%d", exp_lc_count);
  uint8_t lc_count;
  TRY(dif_lc_ctrl_get_attempts(lc_ctrl, &lc_count));
  TRY_CHECK(lc_count == exp_lc_count,
            "LC_count error, expected %d but actual count is %d", exp_lc_count,
            lc_count);
  return OK_STATUS();
}

status_t lc_ctrl_testutils_check_lc_state(const dif_lc_ctrl_t *lc_ctrl,
                                          dif_lc_ctrl_state_t exp_lc_state) {
  LOG_INFO("Read LC state and check with expect_state=%d", exp_lc_state);
  dif_lc_ctrl_state_t lc_state;
  TRY(dif_lc_ctrl_get_state(lc_ctrl, &lc_state));
  TRY_CHECK(lc_state == exp_lc_state,
            "LC_state error, expected %d but actual state is %d", exp_lc_state,
            lc_state);
  return OK_STATUS();
}

status_t lc_ctrl_testutils_operational_state_check(
    const dif_lc_ctrl_t *lc_ctrl) {
  dif_lc_ctrl_state_t state;
  TRY(dif_lc_ctrl_get_state(lc_ctrl, &state));
  if (state == kDifLcCtrlStateProd || state == kDifLcCtrlStateProdEnd ||
      state == kDifLcCtrlStateDev) {
    return OK_STATUS();
  }
  return FAILED_PRECONDITION();
}
