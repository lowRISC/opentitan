// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_soc_proxy.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/soc_proxy_regs.h"
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
  dif_pwrmgr_request_sources_t reset_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      pwrmgr, kDifPwrmgrReqTypeReset, dt_soc_proxy_instance_id(kDtSocProxy),
      kDtSocProxyResetReqExternal, &reset_sources));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));
  LOG_INFO("External resets enabled.");

  // Give DV environment time for triggering external reset.
  busy_spin_micros(1000);

  // This should never be reached.
  CHECK(false, "Did not get reset in time!");
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kDtPwrmgrAon, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kDtRstmgrAon, &rstmgr));

  // Behave based on reset reason.
  if (UNWRAP(
          rstmgr_testutils_reset_info_any(&rstmgr, kDifRstmgrResetInfoPor))) {
    after_por(&pwrmgr);
  } else if (UNWRAP(rstmgr_testutils_reset_info_any(
                 &rstmgr, kDifRstmgrResetInfoExternalRst))) {
    // We are done, bail out
  } else {
    // Unexpected reset reason -> fail test.
    return false;
  }

  return true;
}
