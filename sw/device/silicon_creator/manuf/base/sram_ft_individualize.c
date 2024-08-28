// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/hart.h"
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

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;

static manuf_ft_individualize_data_t in_data;
static uint32_t device_id[kHwCfgDeviceIdSizeIn32BitWords];
static uint32_t ast_cfg_data[kFlashInfoAstCalibrationDataSizeIn32BitWords];

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
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
static status_t print_flash_info_0_data_to_console(void) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldDeviceId.page,
      kFlashInfoFieldDeviceId.bank, kFlashInfoFieldDeviceId.partition,
      kFlashInfoPage0Permissions, &byte_address));

  LOG_INFO("Device ID:");
  TRY(manuf_flash_info_field_read(&flash_ctrl_state, kFlashInfoFieldDeviceId,
                                  device_id, kHwCfgDeviceIdSizeIn32BitWords));
  for (size_t i = 0; i < kHwCfgDeviceIdSizeIn32BitWords; ++i) {
    LOG_INFO("0x%x", device_id[i]);
  }

  LOG_INFO("AST Calibration Values:");
  TRY(manuf_flash_info_field_read(
      &flash_ctrl_state, kFlashInfoFieldAstCalibrationData, ast_cfg_data,
      kFlashInfoAstCalibrationDataSizeIn32BitWords));
  for (size_t i = 0; i < kFlashInfoAstCalibrationDataSizeIn32BitWords; ++i) {
    LOG_INFO("0x%x", ast_cfg_data[i]);
  }

  return OK_STATUS();
}

/**
 * Provision OTP {CreatorSw,OwnerSw,Hw}Cfg partitions.
 *
 * Note: CreatorSwCfg partition is not locked yet, as the flash scrambling OTP
 * field is not provisioned until after the Secret1 partition is provisioned
 * during personalization.
 */
static status_t provision(ujson_t *uj) {
  LOG_INFO("Waiting for FT SRAM provisioning data ...");
  TRY(ujson_deserialize_manuf_ft_individualize_data_t(uj, &in_data));
  TRY(manuf_individualize_device_hw_cfg(&flash_ctrl_state, &otp_ctrl,
                                        kFlashInfoPage0Permissions,
                                        in_data.device_id));
  TRY(manuf_individualize_device_creator_sw_cfg(&otp_ctrl, &flash_ctrl_state));
  TRY(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
  LOG_INFO("FT SRAM provisioning done.");
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Print flash data to console (for manual verification purposes) and perform
  // provisioning operations.
  CHECK_STATUS_OK(print_flash_info_0_data_to_console());
  CHECK_STATUS_OK(provision(&uj));

  // Halt the CPU here to enable JTAG to perform an LC transition to mission
  // mode, as ROM execution should be active now.
  abort();

  return true;
}
