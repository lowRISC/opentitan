// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_soc_proxy.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "soc_proxy_regs.h"

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

/**
 * @brief To be executed after external reset request.
 */
void after_ext_rst_req(const dif_rv_plic_t *rv_plic,
                       const dif_soc_proxy_t *soc_proxy) {
  LOG_INFO("Reset on external request.");

  // At this point, we are expecting interrupt requests from DV env.

  // Enable external IRQs in Ibex.
  irq_external_ctrl(true);

  for (unsigned i = 0; i < SOC_PROXY_PARAM_NUM_EXTERNAL_IRQS; i++) {
    const dif_rv_plic_irq_id_t rv_plic_irq =
        (dif_rv_plic_irq_id_t)(kTopDarjeelingPlicIrqIdSocProxyExternal0 + i);
    const dif_rv_plic_target_t rv_plic_target = kTopDarjeelingPlicTargetIbex0;
    const dif_soc_proxy_irq_t soc_proxy_irq = (dif_soc_proxy_irq_t)i;

    // Enable IRQ in SoC Proxy and PLIC.
    CHECK_DIF_OK(dif_soc_proxy_irq_set_enabled(soc_proxy, soc_proxy_irq,
                                               kDifToggleEnabled));
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(rv_plic, rv_plic_irq, 1));
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        rv_plic, rv_plic_irq, rv_plic_target, kDifToggleEnabled));
    LOG_INFO("IRQ %0d enabled.", i);

    for (unsigned num_try = 0; num_try < 10; num_try++) {
      // Wait for interrupt, then check that the expected IRQ is pending in both
      // SoC Proxy and PLIC.
      wait_for_interrupt();
      bool soc_proxy_irq_pending;
      CHECK_DIF_OK(dif_soc_proxy_irq_is_pending(soc_proxy, soc_proxy_irq,
                                                &soc_proxy_irq_pending));
      if (soc_proxy_irq_pending) {
        LOG_INFO("IRQ %0d pending in soc_proxy.", i);
      } else {
        // Not the IRQ we're expecting, wait for another one.
        continue;
      }
      bool rv_plic_irq_pending;
      CHECK_DIF_OK(dif_rv_plic_irq_is_pending(rv_plic, rv_plic_irq,
                                              &rv_plic_irq_pending));
      if (rv_plic_irq_pending) {
        // IRQ pending in PLIC and SoC Proxy, stop trying.
        LOG_INFO("IRQ %0d pending in rv_plic.", i);
        break;
      } else {
        // IRQ pending in SoC Proxy but not PLIC -> error and abort.
        CHECK(false, "Expected IRQ to be pending in soc_proxy AND rv_plic!");
      }
    }

    // Acknowledge and complete IRQ.
    CHECK_DIF_OK(dif_soc_proxy_irq_acknowledge(soc_proxy, soc_proxy_irq));
    CHECK_DIF_OK(
        dif_rv_plic_irq_complete(rv_plic, rv_plic_target, rv_plic_irq));

    // Disable IRQ in PLIC and SoC Proxy.
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        rv_plic, rv_plic_irq, rv_plic_target, kDifToggleDisabled));
    CHECK_DIF_OK(dif_soc_proxy_irq_set_enabled(soc_proxy, soc_proxy_irq,
                                               kDifToggleDisabled));
  }

  // Disable external IRQs in Ibex.
  irq_external_ctrl(false);
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;
  dif_rv_plic_t rv_plic;
  dif_soc_proxy_t soc_proxy;

  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kDtPwrmgrAon, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kDtRstmgrAon, &rstmgr));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, &rv_plic));
  CHECK_DIF_OK(dif_soc_proxy_init_from_dt(kDtSocProxy, &soc_proxy));

  // Behave based on reset reason.
  if (UNWRAP(
          rstmgr_testutils_reset_info_any(&rstmgr, kDifRstmgrResetInfoPor))) {
    after_por(&pwrmgr);
  } else if (UNWRAP(rstmgr_testutils_reset_info_any(
                 &rstmgr, kDifRstmgrResetInfoExternalRst))) {
    after_ext_rst_req(&rv_plic, &soc_proxy);
  } else {
    // Unexpected reset reason -> fail test.
    return false;
  }

  return true;
}
