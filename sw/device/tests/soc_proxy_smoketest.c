// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/pwrmgr/dif/dif_pwrmgr.h"
#include "sw/ip/rstmgr/dif/dif_rstmgr.h"
#include "sw/ip/rstmgr/test/utils/rstmgr_testutils.h"
#include "sw/lib/sw/device/runtime/hart.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * @brief To be executed after power-on reset (POR).
 *
 * @param pwrmgr Pointer to an initialized `dif_pwrmgr_t`.
 *
 * @return Does not return (spinwaits for a timeout and fails a check if the
 *         timeout is reached).
 */
void after_por(dif_pwrmgr_t *pwrmgr) {
  LOG_INFO("Reset after POR.");

  // Enable external reset request in pwrmgr.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));
  LOG_INFO("External resets enabled.");

  // Give DV environment time for triggering external reset.
  busy_spin_micros(1000);

  // This should never be reached.
  CHECK(false, "Did not get reset in time!");
}

/**
 * @brief To be executed after external reset request.
 */
void after_ext_rst_req(void) { LOG_INFO("Reset on external request."); }

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Behave based on reset reason.
  if (UNWRAP(
          rstmgr_testutils_reset_info_any(&rstmgr, kDifRstmgrResetInfoPor))) {
    after_por(&pwrmgr);
  } else if (UNWRAP(rstmgr_testutils_reset_info_any(
                 &rstmgr, kDifRstmgrResetInfoExternal))) {
    after_ext_rst_req();
  } else {
    // Unexpected reset reason -> fail test.
    return false;
  }

  return true;
}
