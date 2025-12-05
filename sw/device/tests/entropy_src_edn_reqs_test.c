// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/aes.h"
#include "hw/top/dt/alert_handler.h"
#include "hw/top/dt/csrng.h"
#include "hw/top/dt/edn.h"
#include "hw/top/dt/entropy_src.h"
#include "hw/top/dt/keymgr.h"
#include "hw/top/dt/kmac.h"
#include "hw/top/dt/otbn.h"
#include "hw/top/dt/otp_ctrl.h"
#include "hw/top/dt/pwrmgr.h"
#include "hw/top/dt/rv_core_ibex.h"
#include "sw/device/lib/arch/boot_stage.h"
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
#include "sw/device/lib/testing/entropy_src_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

#include "hw/top/alert_handler_regs.h"  // Generated.

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
 * Configure the otp to request entropy from the edn.
 */
static void otp_ctrl_test(const dif_otp_ctrl_t *otp) {
  LOG_INFO("%s", __func__);
  // In the owner stage, the OTP direct access interface is blocked by the ePMP
  // so we cannot run this test.
  if (kBootStage == kBootStageOwner) {
    return;
  }

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
  dif_keymgr_state_t expected_stage_before = kBootStage == kBootStageOwner
                                                 ? kDifKeymgrStateOwnerRootKey
                                                 : kDifKeymgrStateReset;
  dif_keymgr_state_t expected_stage_after = kBootStage == kBootStageOwner
                                                ? kDifKeymgrStateDisabled
                                                : kDifKeymgrStateInitialized;
  if (!tested) {
    LOG_INFO("%s", __func__);
    dif_keymgr_config_t config = {.entropy_reseed_interval = 4};
    CHECK_DIF_OK(dif_keymgr_configure(kmgr, config));
    CHECK_STATUS_OK(keymgr_testutils_check_state(kmgr, expected_stage_before));
    CHECK_DIF_OK(dif_keymgr_advance_state(kmgr, NULL));
    CHECK_STATUS_OK(keymgr_testutils_wait_for_operation_done(kmgr));
    CHECK_STATUS_OK(keymgr_testutils_check_state(kmgr, expected_stage_after));
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
  CHECK_DIF_OK(dif_entropy_src_init_from_dt(kDtEntropySrc, &entropy_src));
  CHECK_DIF_OK(dif_csrng_init_from_dt(kDtCsrng, &csrng));
  CHECK_DIF_OK(dif_edn_init_from_dt(kDtEdn0, &edn0));
  CHECK_DIF_OK(dif_edn_init_from_dt(kDtEdn1, &edn1));
  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kDtRvCoreIbex, &ibex));
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kDtPwrmgrAon, &pwrmgr));
  CHECK_DIF_OK(dif_keymgr_init_from_dt(kDtKeymgr, &kmgr));
  CHECK_DIF_OK(dif_otbn_init_from_dt(kDtOtbn, &otbn));
  CHECK_DIF_OK(dif_otp_ctrl_init_from_dt(kDtOtpCtrl, &otp));
  CHECK_DIF_OK(dif_aes_init_from_dt(kDtAes, &aes));
  CHECK_DIF_OK(dif_kmac_init_from_dt(kDtKmac, &kmac));
  CHECK_DIF_OK(dif_alert_handler_init_from_dt(kDtAlertHandler, &alert_handler));
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
    CHECK_STATUS_OK(entropy_testutils_error_check(&csrng, &edn0, &edn1));
  }

  return OK_STATUS();
}

bool test_main(void) {
  test_initialize();

  // The keymgr cannot be initialized after ROM_EXT because the flash controller
  // is locked out with the ePMP.
  if (kBootStage != kBootStageOwner) {
    CHECK_STATUS_OK(keymgr_testutils_init_nvm_then_reset());
  }

  alert_handler_configure(&alert_handler);
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  // ensure health tests are actually running
  CHECK_STATUS_OK(entropy_src_testutils_wait_for_state(
      &entropy_src, kDifEntropySrcMainFsmStateContHTRunning));

  return status_ok(execute_test());
}
