// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/manuf/base/flash_info_permissions.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top/alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false, );

static dif_alert_handler_t alert_handler;
static dif_clkmgr_t clkmgr;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;

static manuf_ft_individualize_data_t in_data;

// Switching to external clocks causes the clocks to be unstable for some time.
// This is used to delay further action when the switch happens.
static const int kSettleDelayMicros = 200;

static size_t alert_nmi_count = 0;

/**
 * Handle NMIs from the alert escalation mechanism.
 *
 * @param exc_info Execution info.
 */
void ottf_external_nmi_handler(uint32_t *exc_info) {
  LOG_INFO("Processing Alert NMI %d ...", alert_nmi_count++);
  ibex_clear_nmi(kIbexNmiSourceAlert);
}

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  TRY(dif_clkmgr_init(mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR),
                      &clkmgr));
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  return OK_STATUS();
}

// For passing into `IBEX_SPIN_FOR`.
static bool did_extclk_settle(const dif_clkmgr_t *clkmgr) {
  bool status;
  CHECK_DIF_OK(dif_clkmgr_external_clock_is_settled(clkmgr, &status));
  return status;
}

static status_t configure_all_alerts(void) {
  // Enable capturing both alert and CPU crashdump info collection.
  rstmgr_alert_info_enable();
  rstmgr_cpu_info_enable();

  // Enable all alerts and configure them in class A.
  for (size_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    TRY(dif_alert_handler_configure_alert(
        &alert_handler, (dif_alert_handler_alert_t)i, kDifAlertHandlerClassA,
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleDisabled));
  }

  // Enable all local alerts and configure them in class A.
  for (size_t i = 0; i < ALERT_HANDLER_PARAM_N_LOC_ALERT; ++i) {
    TRY(dif_alert_handler_configure_local_alert(
        &alert_handler, (dif_alert_handler_local_alert_t)i,
        kDifAlertHandlerClassA,
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleDisabled));
  }

  // Configure class A alert escalation behavior.
  const dif_alert_handler_escalation_phase_t kEscPhases[2] = {
      {
          .phase = kDifAlertHandlerClassStatePhase0,
          .signal = 0,  // NMI
          .duration_cycles = 1000000,
      },
      {
          .phase = kDifAlertHandlerClassStatePhase1,
          .signal = 3,  // SW Reset
          .duration_cycles = 1000,
      },
  };
  dif_alert_handler_class_config_t alert_class_a_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,  // A single alert will trigger escalation.
      .irq_deadline_cycles = 0,    // Disabled.
      .escalation_phases = kEscPhases,
      .escalation_phases_len = ARRAYSIZE(kEscPhases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase0,

  };
  TRY(dif_alert_handler_configure_class(&alert_handler, kDifAlertHandlerClassA,
                                        alert_class_a_config,
                                        /*enabled=*/kDifToggleEnabled,
                                        /*locked=*/kDifToggleDisabled));

  // Enable NMIs from alert escalation.
  ibex_enable_nmi(kIbexNmiSourceAlert);

  return OK_STATUS();
}

/**
 * Provision OTP {CreatorSw,OwnerSw,Hw}Cfg and RotCreatorAuth{Codesign,State}
 * partitions.
 *
 * Note: CreatorSwCfg and OwnerSwCfg partitions are not locked yet, as not
 * all fields can be programmed until the personalization stage.
 */
static status_t provision(ujson_t *uj) {
  // Get host data.
  LOG_INFO("Waiting for FT SRAM provisioning data ...");
  TRY(ujson_deserialize_manuf_ft_individualize_data_t(uj, &in_data));

  // Enable all alerts (and alert NMIs) if requested.
  if (in_data.enable_alerts) {
    TRY(configure_all_alerts());
    LOG_INFO("All alerts and alert NMI enabled.");
  }

  // Enable external clock on silicon platforms if requested.
  if (kDeviceType == kDeviceSilicon && in_data.use_ext_clk) {
    CHECK_DIF_OK(dif_clkmgr_external_clock_set_enabled(&clkmgr,
                                                       /*is_low_speed=*/true));
    IBEX_SPIN_FOR(did_extclk_settle(&clkmgr), kSettleDelayMicros);
    LOG_INFO("External clock enabled.");
  }

  // Turn off OTP runtime checks.
  TRY(dif_otp_ctrl_configure(
      &otp_ctrl,
      (dif_otp_ctrl_config_t){
          .check_timeout = 0,            // Disable the check timeout mechanism.
          .integrity_period_mask = 0,    // Disable integrity checks.
          .consistency_period_mask = 0,  // Disable consistency checks.
      }));

  // Perform OTP writes.
  LOG_INFO("Writing HW_CFG* OTP partitions ...");
  TRY(manuf_individualize_device_hw_cfg(&flash_ctrl_state, &otp_ctrl,
                                        kFlashInfoPage0Permissions,
                                        in_data.ft_device_id));
  LOG_INFO("Writing ROT_CREATOR_AUTH_CODESIGN OTP partition ...");
  TRY(manuf_individualize_device_rot_creator_auth_codesign(&otp_ctrl));
  LOG_INFO("Writing ROT_CREATOR_AUTH_STATE OTP partition ...");
  TRY(manuf_individualize_device_rot_creator_auth_state(&otp_ctrl));
  LOG_INFO("Writing OWNER_SW_CFG OTP partition ...");
  TRY(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
  LOG_INFO("Writing CREATOR_SW_CFG OTP partition ...");
  TRY(manuf_individualize_device_creator_sw_cfg(&otp_ctrl, &flash_ctrl_state));

  LOG_INFO("FT SRAM provisioning done.");
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(entropy_complex_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Abort if reset reason is due to an escalation.
  if (rstmgr_is_hw_reset_reason(kDtRstmgrAon, rstmgr_reason_get(),
                                kDtInstanceIdAlertHandler, 0)) {
    LOG_INFO("Reset due to alert escalation ... aborting.");
    abort();
  }

  // Clear the reset reasons.
  rstmgr_reason_clear(UINT8_MAX);

  // Perform provisioning operations.
  CHECK_STATUS_OK(provision(&uj));

  // Halt the CPU here to enable JTAG to perform an LC transition to mission
  // mode, as ROM execution should be active now.
  abort();

  return true;
}
