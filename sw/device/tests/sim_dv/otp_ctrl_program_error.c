// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/*
 TO BE FILLED IN
 */

OTTF_DEFINE_TEST_CONFIG();

static dif_lc_ctrl_t lc_ctrl;

bool test_main(void) {
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc_ctrl));

  // Check lc counter is at max
  lc_ctrl_testutils_check_transition_count(&lc_ctrl, 24);

  // Initiate transition into scrap
  dif_lc_ctrl_token_t zero_token = {0, 0, 0, 0, 0, 0, 0, 0,
                                    0, 0, 0, 0, 0, 0, 0, 0};

  // DV sync message
  LOG_INFO("Begin life cycle transition");

  // Mutex acquire should always succeed, there are no competing agents
  CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc_ctrl));
  CHECK_DIF_OK(dif_lc_ctrl_configure(&lc_ctrl, kDifLcCtrlStateScrap, false,
                                     &zero_token));
  CHECK_DIF_OK(dif_lc_ctrl_transition(&lc_ctrl));

  return true;
}
