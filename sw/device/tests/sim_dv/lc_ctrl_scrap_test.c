// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_lc_ctrl_t lc;

// Symbol that tells if the transition should be done via SW (overriden by
// Host).
static volatile const uint8_t kPerformTransitionBySW = 0;

/**
 * Tests the state transition request handshake between LC_CTRL and OTP_CTRL for
 * transition into `Scrap` state.
 *
 * 1). OTP pre-load image with lc_count = `8`.
 * 2). Program LC state transition request to advance to `Scrap` state,
 * if doing the transition through SW.
 * 3). Return control to Host side.
 * 4). Host will wait for LC_CTRL to enter PostTransition state, then issue a
 * hard reset 5). Host will check the LC state is `Scrap`
 *
 * In summary, this sequence walks through the following LC states:
 * "Any Source State (!Scrap) -> Scrap".
 */

bool execute_lc_ctrl_scrap_test(bool use_ext_clk) {
  if (kPerformTransitionBySW) {
    LOG_INFO("Start LC_CTRL scrap test");

    mmio_region_t lc_reg =
        mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR);
    CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc));

    // Acquire the mutex and perform a transition to SCRAP
    CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc));
    CHECK_DIF_OK(
        dif_lc_ctrl_configure(&lc, kDifLcCtrlStateScrap, use_ext_clk, NULL),
        "LC transition configuration failed!");
    CHECK_DIF_OK(dif_lc_ctrl_transition(&lc), "LC transition failed!");

    LOG_INFO("Waiting for LC transtition done and reboot.");

    // Release the access mutex to LC conroller's registers before
    // finishing the SW.
    CHECK_DIF_OK(dif_lc_ctrl_mutex_release(&lc));

    // At this point a reset should be issued for the new LC state to take
    // effect. However, as we are transitioning into SCRAP, the core won't be
    // able to execute any SW code, so this sequence will never return true.
    // Instead, the reset task will be handled by Host code.
    wait_for_interrupt();
    CHECK(false, "Should have reset before this line.");
  } else {
    LOG_INFO("LC transition is performed by JTAG. Skipping SW...");
  }

  return true;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  return execute_lc_ctrl_scrap_test(/*use_ext_clk=*/false);
}
