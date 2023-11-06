// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_aes_t aes;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_entropy_src_t entropy_src;
static dif_kmac_t kmac;
static dif_keymgr_t kmgr;
static dif_otbn_t otbn;
static dif_otp_ctrl_t otp;
static dif_pwrmgr_t pwrmgr;
static dif_rv_core_ibex_t ibex;
static dif_alert_handler_t alert_handler;
static dif_rv_core_ibex_fpga_info_t fpga_info;

enum {
  kFpgaLoop = 5,
};

OTTF_DEFINE_TEST_CONFIG();

/**
 * Trigger an reseed operation.
 *
 * @param aes Aes dif handle.
 */
static void aes_test(const dif_aes_t *aes) {
  LOG_INFO("%s", __func__);

  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySideload,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationManual,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };
  CHECK_DIF_OK(dif_aes_start(aes, &transaction, /*key=*/NULL, /*iv=*/NULL));
  CHECK_DIF_OK(dif_aes_trigger(aes, kDifAesTriggerPrngReseed));
}

/**
 * Configure the kmac to use entropy from edn to request entropy.
 */
static void kmac_test(dif_kmac_t *kmac) {
  LOG_INFO("%s", __func__);

  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_fast_process = kDifToggleDisabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(kmac, config));
}

/**
 * Configure the opt to request entropy from the edn.
 */
static void otp_ctrl_test(const dif_otp_ctrl_t *otp) {
  LOG_INFO("%s", __func__);

  // For security reasons, the LFSR is periodically reseeded with entropy coming
  // from EDN. Setting the integrity period to a small value will make the
  // otp_ctrl to fetch entropy from EDN.
  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x4,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(otp, config));
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(otp));
}

/**
 * Configure the reseed interval to a short period and
 * advance to the `kDifKeymgrStateInitialized` to request entropy from the edn.
 */
static void keymgr_test(const dif_keymgr_t *kmgr) {
  /**
   * Key manager can only be tested once per boot.
   */
  static bool tested = false;
  if (!tested) {
    LOG_INFO("%s", __func__);
    dif_keymgr_config_t config = {.entropy_reseed_interval = 4};
    CHECK_DIF_OK(dif_keymgr_configure(kmgr, config));
    CHECK_DIF_OK(dif_keymgr_advance_state(kmgr, NULL));
    tested = true;
  }
}

/**
 * Read 4 words of rnd data to request entropy from the edn.
 */
static void ibex_test(const dif_rv_core_ibex_t *ibex) {
  LOG_INFO("%s", __func__);
  for (size_t i = 0; i < 4; i++) {
    uint32_t rnd;
    CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(ibex, &rnd));
  }
}

/**
 * Configure the `alert_handler`to escalate up to phase 0.
 */
static void alert_handler_configure(const dif_alert_handler_t *alert_handler) {
  LOG_INFO("%s", __func__);

  dif_alert_handler_local_alert_t loc_alerts[] = {
      kDifAlertHandlerLocalAlertAlertPingFail};
  dif_alert_handler_class_t loc_alert_classes[] = {kDifAlertHandlerClassB};

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 2000}};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  dif_alert_handler_class_config_t class_configs[] = {class_config,
                                                      class_config};
  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA,
                                         kDifAlertHandlerClassB};
  dif_alert_handler_config_t config = {
      .alerts = NULL,
      .alert_classes = NULL,
      .alerts_len = 0,
      .local_alerts = loc_alerts,
      .local_alert_classes = loc_alert_classes,
      .local_alerts_len = ARRAYSIZE(loc_alerts),
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = 10,
  };
  CHECK_STATUS_OK(alert_handler_testutils_configure_all(alert_handler, config,
                                                        kDifToggleEnabled));
}

/**
 * Trigger fault in the pwrmgr in order to escalate the alert handler.
 */
static void alert_handler_test(const dif_pwrmgr_t *pwrmgr) {
  LOG_INFO("%s", __func__);

  dif_pwrmgr_alert_t alert = kDifPwrmgrAlertFatalFault;
  CHECK_DIF_OK(dif_pwrmgr_alert_force(pwrmgr, alert));
}

void test_initialize(void) {
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR), &ibex));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &kmgr));
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
}

status_t execute_test(void) {
  CHECK_DIF_OK(dif_rv_core_ibex_read_fpga_info(&ibex, &fpga_info));
  uint32_t loop = (fpga_info != 0) ? kFpgaLoop : 1;

  for (size_t i = 0; i < loop; ++i) {
    LOG_INFO("Entropy src test %d/%d", i, loop);
    alert_handler_test(&pwrmgr);
    aes_test(&aes);
    otbn_randomness_test_start(&otbn, /*iters=*/0);
    keymgr_test(&kmgr);
    otp_ctrl_test(&otp);
    kmac_test(&kmac);
    ibex_test(&ibex);

    AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, /*value=*/true,
                                  /*timeout_usec=*/100000);
    CHECK(otbn_randomness_test_end(&otbn, /*skip_otbn_done_check=*/false));
    CHECK_STATUS_OK(keymgr_testutils_wait_for_operation_done(&kmgr));
    CHECK_STATUS_OK(
        keymgr_testutils_check_state(&kmgr, kDifKeymgrStateInitialized));
    CHECK_STATUS_OK(
        entropy_testutils_error_check(&entropy_src, &csrng, &edn0, &edn1));
  }

  return OK_STATUS();
}

bool test_main(void) {
  test_initialize();

  alert_handler_configure(&alert_handler);
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  // ensure health tests are actually running
  CHECK_STATUS_OK(entropy_testutils_wait_for_state(
      &entropy_src, kDifEntropySrcMainFsmStateContHTRunning));

  return status_ok(execute_test());
}
