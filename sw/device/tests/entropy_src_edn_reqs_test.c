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
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(randomness);
OTBN_DECLARE_SYMBOL_ADDR(randomness, rv);
OTBN_DECLARE_SYMBOL_ADDR(randomness, fail_idx);
OTBN_DECLARE_SYMBOL_ADDR(randomness, rnd_out);
OTBN_DECLARE_SYMBOL_ADDR(randomness, urnd_out);

static const otbn_app_t kOtbnAppCfiTest = OTBN_APP_T_INIT(randomness);
static const otbn_addr_t kVarRv = OTBN_ADDR_T_INIT(randomness, rv);
static const otbn_addr_t kVarFailIdx = OTBN_ADDR_T_INIT(randomness, fail_idx);
static const otbn_addr_t kVarRndOut = OTBN_ADDR_T_INIT(randomness, rnd_out);
static const otbn_addr_t kVarUrndOut = OTBN_ADDR_T_INIT(randomness, urnd_out);

const test_config_t kTestConfig;

/**
 * Initialize the aes and start and reseed operation.
 *
 * @param aes Aes dif handle.
 */
static void aes_test(dif_aes_t *aes) {
  LOG_INFO("%s", __func__);

  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), aes));

  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .manual_operation = kDifAesManualOperationManual,
      .key_provider = kDifAesKeySideload,
  };
  CHECK_DIF_OK(dif_aes_start(aes, &transaction, NULL, NULL));
  CHECK_DIF_OK(dif_aes_trigger(aes, kDifAesTriggerPrngReseed));
}

/**
 * Initialized the kmac, configure it to use entropy form edn which is enough
 * the request entropy to the edn.
 */
static void kmac_test(dif_kmac_t *kmac) {
  dif_kmac_operation_state_t kmac_operation_state;

  LOG_INFO("%s", __func__);
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), kmac));

  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_fast_process = kDifToggleDisabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(kmac, config));
}

/**
 * Initialized the opt ctrl and configure it, which would be enough to request
 * entropy to the edn.
 */
static void otp_ctrl_test(dif_otp_ctrl_t *otp) {
  LOG_INFO("%s", __func__);

  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), otp));

  // For security reasons, the LFSR is periodically reseeded with entropy coming
  // from EDN. So by setting the integrity period to a small value will make the
  // otp_ctrl to fetch the EDN.
  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x4,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(otp, config));
  otp_ctrl_testutils_wait_for_dai(otp);
}

/**
 * Initialized the otbn, load the randomness app and start its execution, which
 * will request entropy to the edn.
 */
static void otbn_test(otbn_t *otbn) {
  LOG_INFO("%s", __func__);
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  CHECK(otbn_init(otbn, addr) == kOtbnOk);
  CHECK(otbn_load_app(otbn, kOtbnAppCfiTest) == kOtbnOk);
  CHECK(otbn_execute(otbn) == kOtbnOk);
}

/**
 * Initialized the keymgr, configure the reseed interval to a short period and
 * advance to the `kDifKeymgrStateInitialized`.
 */
static void keymgr_test(dif_keymgr_t *kmgr) {
  LOG_INFO("%s", __func__);
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), kmgr));

  dif_keymgr_config_t config = {.entropy_reseed_interval = 4};
  CHECK_DIF_OK(dif_keymgr_configure(kmgr, config));
  CHECK_DIF_OK(dif_keymgr_advance_state(kmgr, NULL));
}

/**
 * Initialized the `rv_core_ibex`, and request 4 words of rnd data.
 */
static void ibex_test(dif_rv_core_ibex_t *ibex) {
  LOG_INFO("%s", __func__);
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR), ibex));

  for (int i = 0; i < 4; i++) {
    uint32_t rnd;
    CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(ibex, &rnd));
  }
}

/**
 * Initialized the `alert_handler`, configure it up to escalation phase 0 and
 * trigger fault in the pwrmgr.
 */
static void alert_handler_test(dif_alert_handler_t *alert_handler) {
  LOG_INFO("%s", __func__);
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, alert_handler));

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
  alert_handler_testutils_configure_all(alert_handler, config,
                                        kDifToggleEnabled);

  // Trigger the alert handler to escalate.
  dif_pwrmgr_t pwrmgr;
  base_addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(base_addr, &pwrmgr));
  dif_pwrmgr_alert_t alert = kDifPwrmgrAlertFatalFault;
  CHECK_DIF_OK(dif_pwrmgr_alert_force(&pwrmgr, alert));
}

bool test_main() {
  otbn_t otbn;
  dif_aes_t aes;
  dif_kmac_t kmac;
  dif_keymgr_t kmgr;
  dif_otp_ctrl_t otp;
  dif_rv_core_ibex_t ibex;
  dif_alert_handler_t alert_handler;

  entropy_testutils_boot_mode_init();

  // wait 1ms to ensure edn has collected enoguh to get going again
  busy_spin_micros(1000);

  alert_handler_test(&alert_handler);
  aes_test(&aes);
  otbn_test(&otbn);
  keymgr_test(&kmgr);
  otp_ctrl_test(&otp);
  kmac_test(&kmac);
  ibex_test(&ibex);

  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, 100000);
  CHECK(otbn_busy_wait_for_done(&otbn) == kOtbnOk);
  keymgr_testutils_wait_for_operation_done(&kmgr);
  keymgr_testutils_check_state(&kmgr, kDifKeymgrStateInitialized);

  return true;
}
