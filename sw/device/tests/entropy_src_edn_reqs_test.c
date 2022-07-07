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

typedef struct entropy_src_test_context {
  otbn_t otbn;
  dif_aes_t aes;
  dif_kmac_t kmac;
  dif_keymgr_t kmgr;
  dif_otp_ctrl_t otp;
  dif_pwrmgr_t pwrmgr;
  dif_rv_core_ibex_t ibex;
  dif_alert_handler_t alert_handler;
  dif_rv_core_ibex_fpga_info_t fpga_info;
} entropy_src_test_context_t;

enum {
  kFpgaLoop = 5,
};

OTTF_DEFINE_TEST_CONFIG();

/**
 * Trigger an reseed operation.
 *
 * @param aes Aes dif handle.
 */
static void aes_test(entropy_src_test_context_t *ctx) {
  LOG_INFO("%s", __func__);

  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .manual_operation = kDifAesManualOperationManual,
      .key_provider = kDifAesKeySideload,
  };
  CHECK_DIF_OK(dif_aes_start(&ctx->aes, &transaction, NULL, NULL));
  CHECK_DIF_OK(dif_aes_trigger(&ctx->aes, kDifAesTriggerPrngReseed));
}

/**
 * Configure the kmac to use entropy from edn to request entropy.
 */
static void kmac_test(entropy_src_test_context_t *ctx) {
  dif_kmac_operation_state_t kmac_operation_state;

  LOG_INFO("%s", __func__);

  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_fast_process = kDifToggleDisabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(&ctx->kmac, config));
}

/**
 * Configure the opt to request entropy from the edn.
 */
static void otp_ctrl_test(entropy_src_test_context_t *ctx) {
  LOG_INFO("%s", __func__);

  // For security reasons, the LFSR is periodically reseeded with entropy coming
  // from EDN. Setting the integrity period to a small value will make the
  // otp_ctrl to fetch entropy from EDN.
  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x4,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(&ctx->otp, config));
  otp_ctrl_testutils_wait_for_dai(&ctx->otp);
}

/**
 * Load the randomness app and start its execution, which
 * will request entropy from the edn.
 */
static void otbn_test(entropy_src_test_context_t *ctx) {
  LOG_INFO("%s", __func__);

  CHECK(otbn_load_app(&ctx->otbn, kOtbnAppCfiTest) == kOtbnOk);
  CHECK(otbn_execute(&ctx->otbn) == kOtbnOk);
}

/**
 * Configure the reseed interval to a short period and
 * advance to the `kDifKeymgrStateInitialized` to request entropy from the edn.
 */
static void keymgr_test(entropy_src_test_context_t *ctx) {
  /**
   * Key manager can only be tested once per boot.
   */
  static bool tested = false;
  if (!tested) {
    LOG_INFO("%s", __func__);
    dif_keymgr_config_t config = {.entropy_reseed_interval = 4};
    CHECK_DIF_OK(dif_keymgr_configure(&ctx->kmgr, config));
    CHECK_DIF_OK(dif_keymgr_advance_state(&ctx->kmgr, NULL));
    tested = true;
  }
}

/**
 * Read 4 words of rnd data to request entropy from the edn.
 */
static void ibex_test(entropy_src_test_context_t *ctx) {
  LOG_INFO("%s", __func__);

  for (int i = 0; i < 4; i++) {
    uint32_t rnd;
    CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(&ctx->ibex, &rnd));
  }
}

/**
 * Configure the `alert_handler`to escalate up to phase 0.
 */
static void alert_handler_configure(entropy_src_test_context_t *ctx) {
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
  alert_handler_testutils_configure_all(&ctx->alert_handler, config,
                                        kDifToggleEnabled);
}

/**
 * Trigger fault in the pwrmgr in order to escalate the alert handler.
 */
static void alert_handler_test(entropy_src_test_context_t *ctx) {
  LOG_INFO("%s", __func__);

  // Trigger the alert handler to escalate.
  dif_pwrmgr_alert_t alert = kDifPwrmgrAlertFatalFault;
  CHECK_DIF_OK(dif_pwrmgr_alert_force(&ctx->pwrmgr, alert));
}

void test_initialize(entropy_src_test_context_t *ctx) {
  LOG_INFO("%s", __func__);
  entropy_testutils_boot_mode_init();

  mmio_region_t addr =
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(addr, &ctx->alert_handler));
  alert_handler_configure(ctx);

  addr = mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(addr, &ctx->ibex));

  addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(addr, &ctx->pwrmgr));

  addr = mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR);
  CHECK_DIF_OK(dif_keymgr_init(addr, &ctx->kmgr));

  addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  CHECK(otbn_init(&ctx->otbn, addr) == kOtbnOk);

  addr = mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(addr, &ctx->otp));

  addr = mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR);
  CHECK_DIF_OK(dif_aes_init(addr, &ctx->aes));

  addr = mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_kmac_init(addr, &ctx->kmac));
}

/**
 * TODO: Run the test entropy src end reqs in continuous mode
 * (https://github.com/lowRISC/opentitan/issues/13393)
 */
bool test_main() {
  static entropy_src_test_context_t ctx;
  uint32_t loop = 1;
  test_initialize(&ctx);
  CHECK_DIF_OK(dif_rv_core_ibex_read_fpga_info(&ctx.ibex, &ctx.fpga_info));

  // Run multiple times if in a FPGA.
  loop = (ctx.fpga_info != 0) ? kFpgaLoop : loop;

  for (int i = 0; i < loop; ++i) {
    LOG_INFO("Entropy src test %d/%d", i, loop);
    alert_handler_test(&ctx);
    aes_test(&ctx);
    otbn_test(&ctx);
    keymgr_test(&ctx);
    otp_ctrl_test(&ctx);
    kmac_test(&ctx);
    ibex_test(&ctx);

    AES_TESTUTILS_WAIT_FOR_STATUS(&ctx.aes, kDifAesStatusIdle, true, 100000);
    CHECK(otbn_busy_wait_for_done(&ctx.otbn) == kOtbnOk);
    keymgr_testutils_wait_for_operation_done(&ctx.kmgr);
    keymgr_testutils_check_state(&ctx.kmgr, kDifKeymgrStateInitialized);
  }
  return true;
}
