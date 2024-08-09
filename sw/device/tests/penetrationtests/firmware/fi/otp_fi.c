// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/otp_fi.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/firmware/lib/sca_lib.h"
#include "sw/device/tests/penetrationtests/json/otp_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

// NOP macros.
#define NOP1 "addi x0, x0, 0\n"
#define NOP10 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1
#define NOP100 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10
#define NOP1000 \
  NOP100 NOP100 NOP100 NOP100 NOP100 NOP100 NOP100 NOP100 NOP100 NOP100

static dif_otp_ctrl_t otp;

uint32_t
    otp_read32_result_vendor_test_comp[OTP_CTRL_PARAM_VENDOR_TEST_SIZE / 4];
uint32_t otp_read32_result_vendor_test_fi[OTP_CTRL_PARAM_VENDOR_TEST_SIZE / 4];
uint32_t
    otp_read32_result_owner_sw_cfg_comp[OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE / 4];
uint32_t
    otp_read32_result_owner_sw_cfg_fi[OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE / 4];
uint32_t otp_read32_result_hw_cfg_comp[OTP_CTRL_PARAM_HW_CFG0_SIZE / 4];
uint32_t otp_read32_result_hw_cfg_fi[OTP_CTRL_PARAM_HW_CFG0_SIZE / 4];
uint32_t otp_read32_result_life_cycle_comp[OTP_CTRL_PARAM_LIFE_CYCLE_SIZE / 4];
uint32_t otp_read32_result_life_cycle_fi[OTP_CTRL_PARAM_LIFE_CYCLE_SIZE / 4];

void init_otp_mem_dump_buffers(void) {
  for (uint32_t i = 0; i < OTP_CTRL_PARAM_VENDOR_TEST_SIZE / 4; i++) {
    otp_read32_result_vendor_test_comp[i] = 0x00000001;
    otp_read32_result_vendor_test_fi[i] = 0x00000001;
  }
  for (uint32_t i = 0; i < OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE / 4; i++) {
    otp_read32_result_owner_sw_cfg_comp[i] = 0x00000001;
    otp_read32_result_owner_sw_cfg_fi[i] = 0x00000001;
  }
  for (uint32_t i = 0; i < OTP_CTRL_PARAM_HW_CFG0_SIZE / 4; i++) {
    otp_read32_result_hw_cfg_comp[i] = 0x00000001;
    otp_read32_result_hw_cfg_fi[i] = 0x00000001;
  }
  for (uint32_t i = 0; i < OTP_CTRL_PARAM_LIFE_CYCLE_SIZE / 4; i++) {
    otp_read32_result_life_cycle_comp[i] = 0x00000001;
    otp_read32_result_life_cycle_fi[i] = 0x00000001;
  }
}

status_t otp_vendor_test_dump(uint32_t *buffer) {
  // Read VENDOR_TEST partition
  TRY(otp_ctrl_testutils_dai_read32_array(&otp, kDifOtpCtrlPartitionVendorTest,
                                          0, buffer,
                                          OTP_CTRL_PARAM_VENDOR_TEST_SIZE / 4));

  return OK_STATUS();
}

status_t otp_owner_sw_cfg_dump(uint32_t *buffer) {
  // Read OWNER_SW_CFG partition
  TRY(otp_ctrl_testutils_dai_read32_array(
      &otp, kDifOtpCtrlPartitionOwnerSwCfg, 0, buffer,
      OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE / 4));

  return OK_STATUS();
}

status_t otp_hw_cfg_dump(uint32_t *buffer) {
  // Read HW_CFG partition
  TRY(otp_ctrl_testutils_dai_read32_array(&otp, kDifOtpCtrlPartitionHwCfg0, 0,
                                          buffer,
                                          OTP_CTRL_PARAM_HW_CFG0_SIZE / 4));

  return OK_STATUS();
}

status_t otp_life_cycle_dump(uint32_t *buffer) {
  // Read LIFE_CYCLE partition
  TRY(otp_ctrl_testutils_dai_read32_array(&otp, kDifOtpCtrlPartitionLifeCycle,
                                          0, buffer,
                                          OTP_CTRL_PARAM_LIFE_CYCLE_SIZE / 4));

  return OK_STATUS();
}

status_t handle_otp_fi_hw_cfg(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Read OTP partition for comparison values
  TRY(otp_hw_cfg_dump(otp_read32_result_hw_cfg_comp));

  // FI code target.
  sca_set_trigger_high();

  // Point for FI
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);

  sca_set_trigger_low();

  // Read OTP partition again to see if values changed
  TRY(otp_hw_cfg_dump(otp_read32_result_hw_cfg_fi));

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Get OTP CTRL status
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(&otp, &status));

  // Send result & status codes to host.
  otp_fi_hwcfg_partition_t uj_output;
  for (uint32_t i = 0; i < OTP_CTRL_PARAM_HW_CFG0_SIZE / 4; i++) {
    uj_output.hw_cfg_comp[i] = otp_read32_result_hw_cfg_comp[i];
    uj_output.hw_cfg_fi[i] = otp_read32_result_hw_cfg_fi[i];
  }
  uj_output.otp_status_codes = status.codes;
  memcpy(uj_output.otp_error_causes, (uint8_t *)status.causes,
         kDifOtpCtrlStatusCodeHasCauseLast + 1);
  uj_output.alerts[0] = reg_alerts.alerts[0];
  uj_output.alerts[1] = reg_alerts.alerts[1];
  uj_output.alerts[2] = reg_alerts.alerts[2];
  RESP_OK(ujson_serialize_otp_fi_hwcfg_partition_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otp_fi_init(ujson_t *uj) {
  sca_select_trigger_type(kScaTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // sca_init is not needed. kScaTriggerSourceAes is selected as a placeholder.
  sca_init(kScaTriggerSourceAes,
           kScaPeripheralIoDiv4 | kScaPeripheralEdn | kScaPeripheralCsrng |
               kScaPeripheralEntropy | kScaPeripheralAes | kScaPeripheralHmac |
               kScaPeripheralKmac | kScaPeripheralOtbn);

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  sca_configure_alert_handler();

  // Disable the instruction cache and dummy instructions for FI attacks.
  sca_configure_cpu();

  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  init_otp_mem_dump_buffers();

  return OK_STATUS();
}

status_t handle_otp_fi_life_cycle(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Read OTP partition for comparison values
  TRY(otp_life_cycle_dump(otp_read32_result_life_cycle_comp));

  // FI code target.
  sca_set_trigger_high();

  // Point for FI
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);

  sca_set_trigger_low();

  // Read OTP partition again to see if values changed
  TRY(otp_life_cycle_dump(otp_read32_result_life_cycle_fi));

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Get OTP CTRL status
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(&otp, &status));

  // Send result & status codes to host.
  otp_fi_lifecycle_partition_t uj_output;
  for (uint32_t i = 0; i < OTP_CTRL_PARAM_LIFE_CYCLE_SIZE / 4; i++) {
    uj_output.life_cycle_comp[i] = otp_read32_result_life_cycle_comp[i];
    uj_output.life_cycle_fi[i] = otp_read32_result_life_cycle_fi[i];
  }
  uj_output.otp_status_codes = status.codes;
  memcpy(uj_output.otp_error_causes, (uint8_t *)status.causes,
         kDifOtpCtrlStatusCodeHasCauseLast + 1);
  uj_output.alerts[0] = reg_alerts.alerts[0];
  uj_output.alerts[1] = reg_alerts.alerts[1];
  uj_output.alerts[2] = reg_alerts.alerts[2];
  RESP_OK(ujson_serialize_otp_fi_lifecycle_partition_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otp_fi_owner_sw_cfg(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Read OTP partition for comparison values
  TRY(otp_owner_sw_cfg_dump(otp_read32_result_owner_sw_cfg_comp));

  // FI code target.
  sca_set_trigger_high();

  // Point for FI
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);

  sca_set_trigger_low();

  // Read OTP partition again to see if values changed
  TRY(otp_owner_sw_cfg_dump(otp_read32_result_owner_sw_cfg_fi));

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Get OTP CTRL status
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(&otp, &status));

  // Send result & status codes to host.
  otp_fi_ownerswcfg_partition_t uj_output;
  for (uint32_t i = 0; i < OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE / 4; i++) {
    uj_output.owner_sw_cfg_comp[i] = otp_read32_result_owner_sw_cfg_comp[i];
    uj_output.owner_sw_cfg_fi[i] = otp_read32_result_owner_sw_cfg_fi[i];
  }
  uj_output.otp_status_codes = status.codes;
  memcpy(uj_output.otp_error_causes, (uint8_t *)status.causes,
         kDifOtpCtrlStatusCodeHasCauseLast + 1);
  uj_output.alerts[0] = reg_alerts.alerts[0];
  uj_output.alerts[1] = reg_alerts.alerts[1];
  uj_output.alerts[2] = reg_alerts.alerts[2];
  RESP_OK(ujson_serialize_otp_fi_ownerswcfg_partition_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otp_fi_vendor_test(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Read OTP partition for comparison values
  TRY(otp_vendor_test_dump(otp_read32_result_vendor_test_comp));

  // FI code target.
  sca_set_trigger_high();

  // Point for FI
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);
  asm volatile(NOP1000);

  sca_set_trigger_low();

  // Read OTP partition again to see if values changed
  TRY(otp_vendor_test_dump(otp_read32_result_vendor_test_fi));

  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Get OTP CTRL status
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(&otp, &status));

  // Send result & status codes to host.
  otp_fi_vendortest_partition_t uj_output;
  for (uint32_t i = 0; i < OTP_CTRL_PARAM_VENDOR_TEST_SIZE / 4; i++) {
    uj_output.vendor_test_comp[i] = otp_read32_result_vendor_test_comp[i];
    uj_output.vendor_test_fi[i] = otp_read32_result_vendor_test_fi[i];
  }
  uj_output.otp_status_codes = status.codes;
  memcpy(uj_output.otp_error_causes, (uint8_t *)status.causes,
         kDifOtpCtrlStatusCodeHasCauseLast + 1);
  uj_output.alerts[0] = reg_alerts.alerts[0];
  uj_output.alerts[1] = reg_alerts.alerts[1];
  uj_output.alerts[2] = reg_alerts.alerts[2];
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
