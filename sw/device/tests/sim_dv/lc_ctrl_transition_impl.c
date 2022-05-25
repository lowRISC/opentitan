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
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define LC_TOKEN_SIZE 16

static dif_lc_ctrl_t lc;

const test_config_t kTestConfig;

/**
 * Track number of iterations of this C test.
 *
 * From the software / compiler's perspective, this is a constant (hence the
 * `const` qualifier). However, the external DV testbench finds this symbol's
 * address and modifies it via backdoor, to track how many transactions have
 * been sent. Hence, we add the `volatile` keyword to prevent the compiler from
 * optimizing it out.
 * The `const` is needed to put it in the .rodata section, otherwise it gets
 * placed in .data section in the main SRAM. We cannot backdoor write anything
 * in SRAM at the start of the test because the CRT init code wipes it to 0s.
 */
static volatile const uint8_t kTestIterationCount = 0x0;

// LC exit token value for LC state transition.
static volatile const uint8_t kLcExitToken[LC_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

static void check_lc_state_transition_count(uint8_t exp_lc_count) {
  LOG_INFO("Read LC count and check with expect_val=%0d", exp_lc_count);
  uint8_t lc_count;
  CHECK(dif_lc_ctrl_get_attempts(&lc, &lc_count) == kDifOk,
        "Read lc_count register failed!");
  CHECK(lc_count == exp_lc_count,
        "LC_count error, expected %0d but actual count is %0d", exp_lc_count,
        lc_count);
}

/**
 * Tests the state transition request handshake between LC_CTRL and OTP_CTRL.
 *
 * 1). OTP pre-load image with lc_count = `8`.
 * 2). Backdoor write OTP's LC parition to `TestLocked1` state, and backdoor
 * write OTP's `test_exit` token and `test_unlock` token to match the rand
 * patterns.
 * 3). `TestLocked1` state disabled CPU, so external testbench will drive JTAG
 * interface to transit to `TestUnlocked2` state and increment the LC_CNT.
 * 4). When LC_CTRL is ready, check LC_CNT and LC_STATE register.
 * 5). Program LC state transition request to advance to `Prod` state.
 * 6). Issue hard reset.
 * 7). Wait for LC_CTRL is ready, then check if LC_STATE advanced to `Dev`
 * state, and lc_count advanced to `9`.
 * 8). Issue hard reset and override OTP's LC partition, and reset LC state to
 * `TestUnlocked2` state.
 */

bool test_main(void) {
  LOG_INFO("Start LC_CTRL transition test.");

  mmio_region_t lc_reg = mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc));

  LOG_INFO("Read and check LC state.");
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));

  // The OTP preload image hardcodes the initial LC state transition count to 8.
  // With each iteration of test, there are two LC_CTRL state transitions.
  // And the first LC_CTRL state transition is done via external JTAG interface.
  // `kTestIterationCount` starts with 1 in SystemVerilog.
  const uint8_t kLcStateTransitionCount = 8 + 1 + (kTestIterationCount - 1) * 2;

  if (curr_state == kDifLcCtrlStateTestUnlocked2) {
    // LC TestUnlocked2 is the intial test state for this sequence.
    // The sequence will check if lc_count matches the preload value.
    check_lc_state_transition_count(kLcStateTransitionCount);

    // Request lc_state transfer to Dev state.
    dif_lc_ctrl_token_t token;
    dif_lc_ctrl_settings_t settings;
    settings.clock_select = kDifLcCtrlInternalClockEn;
    for (int i = 0; i < LC_TOKEN_SIZE; i++) {
      token.data[i] = kLcExitToken[i];
    }
    CHECK(dif_lc_ctrl_mutex_try_acquire(&lc) == kDifOk);
    CHECK(dif_lc_ctrl_transition(&lc, kDifLcCtrlStateDev, &token, &settings) ==
              kDifOk,
          "LC_transition failed!");

    LOG_INFO("Waiting for LC transtition done and reboot.");
    wait_for_interrupt();

  } else {
    // LC Dev is the requested state from previous lc_state transition request.
    // Once the sequence checks current state and count via CSRs, the test can
    // exit successfully.
    CHECK(curr_state == kDifLcCtrlStateDev, "State transition failed!");
    check_lc_state_transition_count(kLcStateTransitionCount + 1);
    return true;
  }

  return false;
}
