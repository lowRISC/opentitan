// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
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
#include "sw/device/silicon_creator/manuf/base/flash_info_permissions.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false, );

static dif_clkmgr_t clkmgr;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;

static manuf_ft_individualize_data_t in_data;
static uint32_t cp_device_id[kFlashInfoFieldCpDeviceIdSizeIn32BitWords];
static uint32_t ast_cfg_data[kFlashInfoAstCalibrationDataSizeIn32BitWords];

// Switching to external clocks causes the clocks to be unstable for some time.
// This is used to delay further action when the switch happens.
static const int kSettleDelayMicros = 200;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
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

/**
 * Print data stored in flash info page 0 to console for manual verification
 * purposes during silicon bring-up.
 */
static status_t read_and_print_flash_and_ast_data(void) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldCpDeviceId.page,
      kFlashInfoFieldCpDeviceId.bank, kFlashInfoFieldCpDeviceId.partition,
      kFlashInfoPage0Permissions, &byte_address));

  LOG_INFO("CP Device ID:");
  TRY(manuf_flash_info_field_read(&flash_ctrl_state, kFlashInfoFieldCpDeviceId,
                                  cp_device_id,
                                  kFlashInfoFieldCpDeviceIdSizeIn32BitWords));
  for (size_t i = 0; i < kHwCfgDeviceIdSizeIn32BitWords; ++i) {
    LOG_INFO("0x%08x", cp_device_id[i]);
  }

  LOG_INFO("AST Calibration Values (in flash):");
  TRY(manuf_flash_info_field_read(
      &flash_ctrl_state, kFlashInfoFieldAstCalibrationData, ast_cfg_data,
      kFlashInfoAstCalibrationDataSizeIn32BitWords));
  for (size_t i = 0; i < kFlashInfoAstCalibrationDataSizeIn32BitWords; ++i) {
    LOG_INFO("Word %d = 0x%08x", i, ast_cfg_data[i]);
  }

  LOG_INFO("AST Calibration Values (in CSRs):");
  for (size_t i = 0; i < kFlashInfoAstCalibrationDataSizeIn32BitWords; ++i) {
    LOG_INFO(
        "Word %d = 0x%08x", i,
        abs_mmio_read32(TOP_EARLGREY_AST_BASE_ADDR + i * sizeof(uint32_t)));
  }

  return OK_STATUS();
}

// For passing into `IBEX_SPIN_FOR`.
static bool did_extclk_settle(const dif_clkmgr_t *clkmgr) {
  bool status;
  CHECK_DIF_OK(dif_clkmgr_external_clock_is_settled(clkmgr, &status));
  return status;
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

  // Enable external clock on silicon platforms if requested.
  if (kDeviceType == kDeviceSilicon && in_data.use_ext_clk) {
    CHECK_DIF_OK(dif_clkmgr_external_clock_set_enabled(&clkmgr,
                                                       /*is_low_speed=*/true));
    IBEX_SPIN_FOR(did_extclk_settle(&clkmgr), kSettleDelayMicros);
    LOG_INFO("External clock enabled.");
  }

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

  // Read and log flash and AST data to console (for manual verification
  // purposes), and perform provisioning operations.
  CHECK_STATUS_OK(read_and_print_flash_and_ast_data());

  // Perform provisioning operations.
  CHECK_STATUS_OK(provision(&uj));

  // Halt the CPU here to enable JTAG to perform an LC transition to mission
  // mode, as ROM execution should be active now.
  abort();

  return true;
}
