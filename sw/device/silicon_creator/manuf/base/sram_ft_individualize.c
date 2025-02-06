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
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/manuf/base/flash_info_permissions.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top/alert_handler_regs.h"  // Generated.
#include "hw/top/ast_regs.h"            // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false, );

static dif_alert_handler_t alert_handler;
static dif_clkmgr_t clkmgr;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_gpio_t gpio;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;

static manuf_ft_individualize_data_t in_data;

// Switching to external clocks causes the clocks to be unstable for some time.
// This is used to delay further action when the switch happens.
static const int kSettleDelayMicros = 200;

// Number of NMIs seen as a result of alerts firing.
static size_t alert_nmi_count = 0;

// OTP programming indicator GPIOs.
static const dif_gpio_pin_t kGpioPinOtpDaiWaitHook = 0;
static const dif_gpio_pin_t kGpioPinOtpDaiWriteHook = 1;
static const dif_gpio_pin_t kGpioPinOtpDaiReadHook = 2;
static const dif_gpio_pin_t kGpioPinOtpDaiErrorCheckHook = 3;

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
  TRY(dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
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

static status_t configure_gpio_indicators(void) {
  TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc9,
                               kTopEarlgreyPinmuxOutselGpioGpio0));
  TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc10,
                               kTopEarlgreyPinmuxOutselGpioGpio1));
  TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc11,
                               kTopEarlgreyPinmuxOutselGpioGpio2));
  TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc12,
                               kTopEarlgreyPinmuxOutselGpioGpio3));
  TRY(dif_gpio_output_set_enabled_all(&gpio, 0xF));  // Enable first 4 GPIOs.
  TRY(dif_gpio_write_all(&gpio, /*write_val=*/0));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_wait_for_dai_pre_hook(
    const dif_otp_ctrl_t *otp_ctrl) {
  TRY(dif_gpio_write(&gpio, kGpioPinOtpDaiWaitHook, true));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_wait_for_dai_post_hook(
    const dif_otp_ctrl_t *otp_ctrl) {
  TRY(dif_gpio_write(&gpio, kGpioPinOtpDaiWaitHook, false));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_dai_write_pre_hook(const dif_otp_ctrl_t *otp_ctrl) {
  TRY(dif_gpio_write(&gpio, kGpioPinOtpDaiWriteHook, true));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_dai_write_post_hook(
    const dif_otp_ctrl_t *otp_ctrl) {
  TRY(dif_gpio_write(&gpio, kGpioPinOtpDaiWriteHook, false));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_dai_read_pre_hook(const dif_otp_ctrl_t *otp_ctrl) {
  TRY(dif_gpio_write(&gpio, kGpioPinOtpDaiReadHook, true));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_dai_read_post_hook(const dif_otp_ctrl_t *otp_ctrl) {
  TRY(dif_gpio_write(&gpio, kGpioPinOtpDaiReadHook, false));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_dai_write_pre_error_check_hook(
    const dif_otp_ctrl_t *otp_ctrl) {
  TRY(dif_gpio_write(&gpio, kGpioPinOtpDaiErrorCheckHook, true));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_dai_write_post_error_check_hook(
    const dif_otp_ctrl_t *otp_ctrl) {
  TRY(dif_gpio_write(&gpio, kGpioPinOtpDaiErrorCheckHook, false));
  return OK_STATUS();
}

/**
 * Patch AST config if patch exists in flash info page 0.
 */
static status_t patch_ast_config_value(void) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldAstIndividPatchAddr.page,
      kFlashInfoFieldAstIndividPatchAddr.bank,
      kFlashInfoFieldAstIndividPatchAddr.partition, kFlashInfoPage0Permissions,
      &byte_address));

  // Read patch address and value from flash info 0.
  uint32_t ast_patch_addr_offset;
  uint32_t ast_patch_value;
  TRY(manuf_flash_info_field_read(
      &flash_ctrl_state, kFlashInfoFieldAstIndividPatchAddr,
      &ast_patch_addr_offset,
      kFlashInfoFieldAstIndividPatchAddrSizeIn32BitWords));
  TRY(manuf_flash_info_field_read(
      &flash_ctrl_state, kFlashInfoFieldAstIndividPatchVal, &ast_patch_value,
      kFlashInfoFieldAstIndividPatchValSizeIn32BitWords));
  LOG_INFO("AST patch address offset = 0x%08x", ast_patch_addr_offset);
  LOG_INFO("AST patch address value  = 0x%08x", ast_patch_value);

  // Check the address is within range before programming.
  // Check the value is non-zero and not all ones before programming.
  if (kDeviceType == kDeviceSilicon || kDeviceType == kDeviceSimDV) {
    TRY_CHECK(ast_patch_addr_offset > AST_REGAL_REG_OFFSET);
    TRY_CHECK(ast_patch_value != 0 && ast_patch_value != UINT32_MAX);
  }

  // Write patch value.
  abs_mmio_write32(
      TOP_EARLGREY_AST_BASE_ADDR + ast_patch_addr_offset * sizeof(uint32_t),
      ast_patch_value);

  // Read back AST calibration values loaded into CSRs.
  LOG_INFO("AST Calibration Values (in CSRs):");
  for (size_t i = 0; i < kFlashInfoAstCalibrationDataSizeIn32BitWords; ++i) {
    LOG_INFO(
        "Word %d = 0x%08x", i,
        abs_mmio_read32(TOP_EARLGREY_AST_BASE_ADDR + i * sizeof(uint32_t)));
  }

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
  if ((kDeviceType == kDeviceSilicon || kDeviceType == kDeviceSimDV) &&
      in_data.use_ext_clk) {
    TRY(dif_clkmgr_external_clock_set_enabled(&clkmgr,
                                              /*is_low_speed=*/true));
    IBEX_SPIN_FOR(did_extclk_settle(&clkmgr), kSettleDelayMicros);
    LOG_INFO("External clock enabled.");
  }

  // Patch AST config if requested.
  if (in_data.patch_ast) {
    TRY(patch_ast_config_value());
  }

  // Enable GPIO indicators during OTP writes.
  TRY(configure_gpio_indicators());

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
