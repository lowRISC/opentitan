// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/otp_fi.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/otp_fi_commands.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_otp_ctrl_t otp;

enum {
  /**
   * OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE in words.
   */
  kOtpFiOwnerSwCfgSize = OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE / sizeof(uint32_t),
  /**
   * OTP_CTRL_PARAM_VENDOR_TEST_SIZE in words.
   */
  kOtpFiVendorTestSize = OTP_CTRL_PARAM_VENDOR_TEST_SIZE / sizeof(uint32_t),
  /**
   * OTP_CTRL_PARAM_HW_CFG0_SIZE in words.
   */
  kOtpFiHwCfg0Size = OTP_CTRL_PARAM_HW_CFG0_SIZE / sizeof(uint32_t),
  /**
   * OTP_CTRL_PARAM_LIFE_CYCLE_SIZE in words.
   */
  kOtpFiLifeCycleSize = OTP_CTRL_PARAM_LIFE_CYCLE_SIZE / sizeof(uint32_t),
};

uint32_t otp_read32_result_vendor_test_comp[kOtpFiVendorTestSize];
uint32_t otp_read32_result_vendor_test_fi[kOtpFiVendorTestSize];
uint32_t otp_read32_result_owner_sw_cfg_comp[kOtpFiOwnerSwCfgSize];
uint32_t otp_read32_result_owner_sw_cfg_fi[kOtpFiOwnerSwCfgSize];
uint32_t otp_read32_result_hw_cfg_comp[kOtpFiHwCfg0Size];
uint32_t otp_read32_result_hw_cfg_fi[kOtpFiHwCfg0Size];
uint32_t otp_read32_result_life_cycle_comp[kOtpFiLifeCycleSize];
uint32_t otp_read32_result_life_cycle_fi[kOtpFiLifeCycleSize];

void init_otp_mem_dump_buffers(void) {
  for (uint32_t i = 0; i < kOtpFiVendorTestSize; i++) {
    otp_read32_result_vendor_test_comp[i] = 0x00000001;
    otp_read32_result_vendor_test_fi[i] = 0x00000001;
  }
  for (uint32_t i = 0; i < kOtpFiOwnerSwCfgSize; i++) {
    otp_read32_result_owner_sw_cfg_comp[i] = 0x00000001;
    otp_read32_result_owner_sw_cfg_fi[i] = 0x00000001;
  }
  for (uint32_t i = 0; i < kOtpFiHwCfg0Size; i++) {
    otp_read32_result_hw_cfg_comp[i] = 0x00000001;
    otp_read32_result_hw_cfg_fi[i] = 0x00000001;
  }
  for (uint32_t i = 0; i < kOtpFiLifeCycleSize; i++) {
    otp_read32_result_life_cycle_comp[i] = 0x00000001;
    otp_read32_result_life_cycle_fi[i] = 0x00000001;
  }
}

status_t otp_vendor_test_dump(uint32_t *buffer) {
  // Read VENDOR_TEST partition
  TRY(otp_ctrl_testutils_dai_read32_array(&otp, kDifOtpCtrlPartitionVendorTest,
                                          0, buffer, kOtpFiVendorTestSize));

  return OK_STATUS();
}

status_t otp_owner_sw_cfg_dump(uint32_t *buffer) {
  // Read OWNER_SW_CFG partition
  TRY(otp_ctrl_testutils_dai_read32_array(&otp, kDifOtpCtrlPartitionOwnerSwCfg,
                                          0, buffer, kOtpFiOwnerSwCfgSize));

  return OK_STATUS();
}

status_t otp_hw_cfg_dump(uint32_t *buffer) {
  // Read HW_CFG partition
  TRY(otp_ctrl_testutils_dai_read32_array(&otp, kDifOtpCtrlPartitionHwCfg0, 0,
                                          buffer, kOtpFiHwCfg0Size));

  return OK_STATUS();
}

status_t otp_life_cycle_dump(uint32_t *buffer) {
  // Read LIFE_CYCLE partition
  TRY(otp_ctrl_testutils_dai_read32_array(&otp, kDifOtpCtrlPartitionLifeCycle,
                                          0, buffer, kOtpFiLifeCycleSize));

  return OK_STATUS();
}

status_t handle_otp_fi_hw_cfg(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Read OTP partition for comparison values
  TRY(otp_hw_cfg_dump(otp_read32_result_hw_cfg_comp));

  // FI code target.
  pentest_set_trigger_high();

  // Point for FI
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);

  pentest_set_trigger_low();

  // Read OTP partition again to see if values changed
  TRY(otp_hw_cfg_dump(otp_read32_result_hw_cfg_fi));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Get OTP CTRL status
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(&otp, &status));

  // Send result & status codes to host.
  otp_fi_hwcfg_partition_t uj_output;
  memset(uj_output.partition_ref, 0, sizeof(uj_output.partition_ref));
  memset(uj_output.partition_fi, 0, sizeof(uj_output.partition_fi));
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  for (uint32_t i = 0; i < kOtpFiHwCfg0Size; i++) {
    uj_output.partition_ref[i] = otp_read32_result_hw_cfg_comp[i];
    uj_output.partition_fi[i] = otp_read32_result_hw_cfg_fi[i];
    if (uj_output.partition_ref[i] != uj_output.partition_fi[i]) {
      uj_output.data_faulty[i] = true;
    }
  }
  uj_output.otp_status_codes = status.codes;
  memcpy(uj_output.otp_error_causes, (uint8_t *)status.causes,
         kDifOtpCtrlNumberOfCauses);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otp_fi_hwcfg_partition_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otp_fi_init(ujson_t *uj) {
  // Configure the device.
  pentest_setup_device(uj, true, false);

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // pentest_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralAes | kPentestPeripheralHmac |
                   kPentestPeripheralKmac | kPentestPeripheralOtbn);

  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  init_otp_mem_dump_buffers();

  // Sanity check lengths of uJSON buffers.
  TRY_CHECK(kOtpFiOwnerSwCfgSize <= OTPFI_MAX_OWNER_SW_CFG_SIZE);
  TRY_CHECK(kOtpFiVendorTestSize <= OTPFI_MAX_VENDOR_TEST_SIZE);
  TRY_CHECK(kOtpFiHwCfg0Size <= OTPFI_MAX_HW_CFG0_SIZE);
  TRY_CHECK(kOtpFiLifeCycleSize <= OTPFI_MAX_LC_SIZE);

  return OK_STATUS();
}

status_t handle_otp_fi_life_cycle(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Read OTP partition for comparison values
  TRY(otp_life_cycle_dump(otp_read32_result_life_cycle_comp));

  // FI code target.
  pentest_set_trigger_high();

  // Point for FI
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);

  pentest_set_trigger_low();

  // Read OTP partition again to see if values changed
  TRY(otp_life_cycle_dump(otp_read32_result_life_cycle_fi));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Get OTP CTRL status
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(&otp, &status));

  // Send result & status codes to host.
  otp_fi_lifecycle_partition_t uj_output;
  memset(uj_output.partition_ref, 0, sizeof(uj_output.partition_ref));
  memset(uj_output.partition_fi, 0, sizeof(uj_output.partition_fi));
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  for (uint32_t i = 0; i < kOtpFiLifeCycleSize; i++) {
    uj_output.partition_ref[i] = otp_read32_result_life_cycle_comp[i];
    uj_output.partition_fi[i] = otp_read32_result_life_cycle_fi[i];
    if (uj_output.partition_ref[i] != uj_output.partition_fi[i]) {
      uj_output.data_faulty[i] = true;
    }
  }
  uj_output.otp_status_codes = status.codes;
  memcpy(uj_output.otp_error_causes, (uint8_t *)status.causes,
         kDifOtpCtrlNumberOfCauses);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otp_fi_lifecycle_partition_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otp_fi_owner_sw_cfg(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Read OTP partition for comparison values
  TRY(otp_owner_sw_cfg_dump(otp_read32_result_owner_sw_cfg_comp));

  // FI code target.
  pentest_set_trigger_high();

  // Point for FI
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);

  pentest_set_trigger_low();

  // Read OTP partition again to see if values changed
  TRY(otp_owner_sw_cfg_dump(otp_read32_result_owner_sw_cfg_fi));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Get OTP CTRL status
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(&otp, &status));

  // Send result & status codes to host.
  otp_fi_ownerswcfg_partition_t uj_output;
  memset(uj_output.partition_ref, 0, sizeof(uj_output.partition_ref));
  memset(uj_output.partition_fi, 0, sizeof(uj_output.partition_fi));
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  for (uint32_t i = 0; i < kOtpFiOwnerSwCfgSize; i++) {
    uj_output.partition_ref[i] = otp_read32_result_owner_sw_cfg_comp[i];
    uj_output.partition_fi[i] = otp_read32_result_owner_sw_cfg_fi[i];
    if (uj_output.partition_ref[i] != uj_output.partition_fi[i]) {
      uj_output.data_faulty[i] = true;
    }
  }
  uj_output.otp_status_codes = status.codes;
  memcpy(uj_output.otp_error_causes, (uint8_t *)status.causes,
         kDifOtpCtrlNumberOfCauses);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otp_fi_ownerswcfg_partition_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otp_fi_vendor_test(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Read OTP partition for comparison values
  TRY(otp_vendor_test_dump(otp_read32_result_vendor_test_comp));

  // FI code target.
  pentest_set_trigger_high();

  // Point for FI
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);

  pentest_set_trigger_low();

  // Read OTP partition again to see if values changed
  TRY(otp_vendor_test_dump(otp_read32_result_vendor_test_fi));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Get OTP CTRL status
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(&otp, &status));

  // Send result & status codes to host.
  otp_fi_vendortest_partition_t uj_output;
  memset(uj_output.partition_ref, 0, sizeof(uj_output.partition_ref));
  memset(uj_output.partition_fi, 0, sizeof(uj_output.partition_fi));
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  for (uint32_t i = 0; i < kOtpFiVendorTestSize; i++) {
    uj_output.partition_ref[i] = otp_read32_result_vendor_test_comp[i];
    uj_output.partition_fi[i] = otp_read32_result_vendor_test_fi[i];
    if (uj_output.partition_ref[i] != uj_output.partition_fi[i]) {
      uj_output.data_faulty[i] = true;
    }
  }
  uj_output.otp_status_codes = status.codes;
  memcpy(uj_output.otp_error_causes, (uint8_t *)status.causes,
         kDifOtpCtrlNumberOfCauses);
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otp_fi_vendortest_partition_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otp_fi(ujson_t *uj) {
  otp_fi_subcommand_t cmd;
  TRY(ujson_deserialize_otp_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kOtpFiSubcommandInit:
      return handle_otp_fi_init(uj);
    case kOtpFiSubcommandVendorTest:
      return handle_otp_fi_vendor_test(uj);
    case kOtpFiSubcommandOwnerSwCfg:
      return handle_otp_fi_owner_sw_cfg(uj);
    case kOtpFiSubcommandHwCfg:
      return handle_otp_fi_hw_cfg(uj);
    case kOtpFiSubcommandLifeCycle:
      return handle_otp_fi_life_cycle(uj);
    default:
      LOG_ERROR("Unrecognized OTP FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
