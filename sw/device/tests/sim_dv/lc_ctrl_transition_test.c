// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define LC_TOKEN_SIZE 16

static dif_lc_ctrl_t lc;

const test_config_t kTestConfig;

// LC exit token value for LC state transition.
static volatile const uint8_t kLcExitToken[LC_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

static void check_lc_state_transition_count(uint8_t exp_lc_count) {
  LOG_INFO("Read LC count and check with expect_val=%0d", exp_lc_count);
  uint8_t lc_count;
  CHECK(dif_lc_ctrl_get_attempts(&lc, &lc_count) == kDifLcCtrlAttemptsOk,
        "Read lc_count register failed!");
  CHECK(lc_count == exp_lc_count,
        "LC_count error, expected %0d but actual count is %0d", exp_lc_count,
        lc_count);
}

/**
 * Tests the state transition request handshake between LC_CTRL and OTP_CTRL.
 *
 * 1). OTP pre-load image with lc_count = `8`.
 * 2). Backdoor write OTP's LC parition to `TestUnlocked2` state, and backdoor
 * write OTP's `test_exit` token to match the pattern
 * `h00_01_02_03_04_05_06_07_08_09_0a_0b_0c_0d`.
 * 3). When LC_CTRL is ready, check LC_CNT and LC_STATE register.
 * 4). Program LC state transition request to advance to `Prod` state.
 * 5). Issue hard reset.
 * 6). Wait for LC_CTRL is ready, then check if LC_STATE advanced to `Dev`
 * state, and lc_count advanced to `9`.
 */

bool test_main(void) {
  LOG_INFO("Start LC_CTRL transition test.");

  mmio_region_t lc_reg = mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  CHECK(dif_lc_ctrl_init((dif_lc_ctrl_params_t){.base_addr = lc_reg}, &lc) ==
        kDifLcCtrlOk);

  LOG_INFO("Read and check LC state.");
  dif_lc_ctrl_state_t curr_state;
  CHECK(dif_lc_ctrl_get_state(&lc, &curr_state) == kDifLcCtrlOk);

  // The OTP preload image hardcode lc_count as 8.
  const uint8_t LcStateTransitionCount = 8;

  if (curr_state == kDifLcCtrlStateTestUnlocked2) {
    // LC TestUnlocked2 is the intial test state for this sequence.
    // The sequence will check if lc_count matches the preload value.
    check_lc_state_transition_count(LcStateTransitionCount);

    // Request lc_state transfer to Dev state.
    dif_lc_ctrl_token_t token;
    dif_lc_ctrl_settings_t settings;
    settings.clock_select = kDifLcCtrlInternalClockEn;
    for (int i = 0; i < LC_TOKEN_SIZE; i++) {
      token.data[i] = kLcExitToken[i];
    }
    CHECK(dif_lc_ctrl_mutex_try_acquire(&lc) == kDifLcCtrlMutexOk);
    CHECK(dif_lc_ctrl_transition(&lc, kDifLcCtrlStateDev, &token, &settings) ==
              kDifLcCtrlMutexOk,
          "LC_transition failed!");

    LOG_INFO("Waiting for LC transtition done and reboot.");
    wait_for_interrupt();

  } else {
    // LC Dev is the requested state from previous lc_state transition request.
    // Once the sequence checks current state and count via CSRs, the test can
    // exit successfully.
    CHECK(curr_state == kDifLcCtrlStateDev, "State transition failed!");
    check_lc_state_transition_count(LcStateTransitionCount + 1);
    return true;
  }

  return false;
}
