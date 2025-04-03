// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/otbn_fi.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/otbn_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

static dif_otbn_t otbn;
static dif_keymgr_t keymgr;

// Indicates whether the load_integrity test is already initialized.
static bool load_integrity_init;
// Indicates whether the char mem test is already initialized.
static bool char_mem_init;
// Indicates whether the char mem test config is valid.
static bool char_mem_test_cfg_valid;
// Reference checksum for the load integrity test.
static uint32_t load_checksum_ref;
// Load integrity test. Initialize OTBN app, load it, and get interface to
// OTBN data memory.
OTBN_DECLARE_APP_SYMBOLS(otbn_load_integrity);
OTBN_DECLARE_SYMBOL_ADDR(otbn_load_integrity, refval1);
OTBN_DECLARE_SYMBOL_ADDR(otbn_load_integrity, refval2);
OTBN_DECLARE_SYMBOL_ADDR(otbn_load_integrity, refval3);
static const otbn_app_t kOtbnAppLoadIntegrity =
    OTBN_APP_T_INIT(otbn_load_integrity);
static const otbn_addr_t kOtbnAppLoadIntegrityRefVal1 =
    OTBN_ADDR_T_INIT(otbn_load_integrity, refval1);
static const otbn_addr_t kOtbnAppLoadIntegrityRefVal2 =
    OTBN_ADDR_T_INIT(otbn_load_integrity, refval2);
static const otbn_addr_t kOtbnAppLoadIntegrityRefVal3 =
    OTBN_ADDR_T_INIT(otbn_load_integrity, refval3);

// Indicates whether the key sideloading test is already initialized.
static bool key_sideloading_init;
// Key sideloading test. Initialize OTBN app, load it, and get interface to
// OTBN data memory.
OTBN_DECLARE_APP_SYMBOLS(otbn_key_sideload);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload, k_s0_l);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload, k_s0_h);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload, k_s1_l);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload, k_s1_h);
const otbn_app_t kOtbnAppKeySideload = OTBN_APP_T_INIT(otbn_key_sideload);
static const otbn_addr_t kOtbnAppKeySideloadks0l =
    OTBN_ADDR_T_INIT(otbn_key_sideload, k_s0_l);
static const otbn_addr_t kOtbnAppKeySideloadks0h =
    OTBN_ADDR_T_INIT(otbn_key_sideload, k_s0_h);
static const otbn_addr_t kOtbnAppKeySideloadks1l =
    OTBN_ADDR_T_INIT(otbn_key_sideload, k_s1_l);
static const otbn_addr_t kOtbnAppKeySideloadks1h =
    OTBN_ADDR_T_INIT(otbn_key_sideload, k_s1_h);

// Config for the otbn.fi.char_mem test.
static bool char_mem_imem;
static bool char_mem_dmem;
static uint32_t char_mem_byte_offset;
static uint32_t char_mem_num_words;

uint32_t key_share_0_l_ref, key_share_0_h_ref;
uint32_t key_share_1_l_ref, key_share_1_h_ref;

// Reference values.
static const uint32_t ref_values[32] = {
    0x1BADB002, 0x8BADF00D, 0xA5A5A5A5, 0xABABABAB, 0xABBABABE, 0xABADCAFE,
    0xBAAAAAAD, 0xBAD22222, 0xBBADBEEF, 0xBEBEBEBE, 0xBEEFCACE, 0xC00010FF,
    0xCAFED00D, 0xCAFEFEED, 0xCCCCCCCC, 0xCDCDCDCD, 0x0D15EA5E, 0xDEAD10CC,
    0xDEADBEEF, 0xDEADCAFE, 0xDEADC0DE, 0xDEADFA11, 0xDEADF00D, 0xDEFEC8ED,
    0xDEADDEAD, 0xD00D2BAD, 0xEBEBEBEB, 0xFADEDEAD, 0xFDFDFDFD, 0xFEE1DEAD,
    0xFEEDFACE, 0xFEEEFEEE};

static const dif_keymgr_versioned_key_params_t kKeyVersionedParamsOTBNFI = {
    .dest = kDifKeymgrVersionedKeyDestSw,
    .salt =  // the salt doesn't really matter here.
    {
        0xb6521d8f,
        0x13a0e876,
        0x1ca1567b,
        0xb4fb0fdf,
        0x9f89bc56,
        0x4bd127c7,
        0x322288d8,
        0xde919d54,
    },
    .version = 0x0,  // specify a low enough version to work with the ROM EXT.
};

/**
 * Clears the OTBN DMEM and IMEM.
 *
 * @returns OK or error.
 */
static status_t clear_otbn(void) {
  // Clear OTBN memory.
  TRY(otbn_dmem_sec_wipe());
  TRY(otbn_imem_sec_wipe());

  return OK_STATUS();
}

/**
 * Read the error bits of the OTBN accelerator.
 *
 * @returns Error bits.
 */
status_t read_otbn_err_bits(dif_otbn_err_bits_t *err_otbn) {
  TRY(dif_otbn_get_err_bits(&otbn, err_otbn));
  return OK_STATUS();
}

/**
 * Read the OTBN load checksum.
 *
 * @returns Load checksum.
 */
status_t read_otbn_load_checksum(uint32_t *checksum) {
  TRY(dif_otbn_get_load_checksum(&otbn, checksum));
  return OK_STATUS();
}

/**
 * Clear the OTBN load checksum.
 */
status_t clear_otbn_load_checksum(void) {
  TRY(dif_otbn_clear_load_checksum(&otbn));
  return OK_STATUS();
}

status_t handle_otbn_fi_char_beq(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_beq);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_beq, res);
  const otbn_app_t kOtbnAppCharBeq = OTBN_APP_T_INIT(otbn_char_beq);
  static const otbn_addr_t kOtbnAppCharBeqRes =
      OTBN_ADDR_T_INIT(otbn_char_beq, res);
  otbn_load_app(kOtbnAppCharBeq);

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read counter (x1) from OTBN data memory.
  otbn_fi_result_cnt_t uj_output;
  uj_output.result = 0;
  otbn_dmem_read(1, kOtbnAppCharBeqRes, &uj_output.result);

  // Read OTBN instruction counter.
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send back to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_result_cnt_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_bn_rshi(ujson_t *uj) {
  // Get big number (2x256 bit).
  otbn_fi_big_num_t uj_data;
  TRY(ujson_deserialize_otbn_fi_big_num_t(uj, &uj_data));

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_bn_rshi);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_bn_rshi, big_num);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_bn_rshi, big_num_out);
  const otbn_app_t kOtbnAppCharBnRshi = OTBN_APP_T_INIT(otbn_char_bn_rshi);
  static const otbn_addr_t kOtbnAppCharBnRshiBigNum =
      OTBN_ADDR_T_INIT(otbn_char_bn_rshi, big_num);
  static const otbn_addr_t kOtbnAppCharBnRshiBigNumOut =
      OTBN_ADDR_T_INIT(otbn_char_bn_rshi, big_num_out);

  // Load app and write received big_num into DMEM.
  otbn_load_app(kOtbnAppCharBnRshi);
  TRY(dif_otbn_dmem_write(&otbn, kOtbnAppCharBnRshiBigNum, uj_data.big_num,
                          sizeof(uj_data.big_num)));

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read big_num_out from OTBN data memory.
  otbn_fi_big_num_out_t uj_output;
  memset(uj_output.big_num, 0, sizeof(uj_output.big_num));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnAppCharBnRshiBigNumOut, uj_output.big_num,
                         sizeof(uj_output.big_num)));

  // Read OTBN instruction counter.
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send back to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_big_num_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_bn_sel(ujson_t *uj) {
  // Get big number (2x256 bit).
  otbn_fi_big_num_t uj_data;
  TRY(ujson_deserialize_otbn_fi_big_num_t(uj, &uj_data));

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_bn_sel);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_bn_sel, big_num);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_bn_sel, big_num_out);
  const otbn_app_t kOtbnAppCharBnSel = OTBN_APP_T_INIT(otbn_char_bn_sel);
  static const otbn_addr_t kOtbnAppCharBnSelBigNum =
      OTBN_ADDR_T_INIT(otbn_char_bn_sel, big_num);
  static const otbn_addr_t kOtbnAppCharBnSelBigNumOut =
      OTBN_ADDR_T_INIT(otbn_char_bn_sel, big_num_out);

  // Load app and write received big_num into DMEM.
  otbn_load_app(kOtbnAppCharBnSel);
  TRY(dif_otbn_dmem_write(&otbn, kOtbnAppCharBnSelBigNum, uj_data.big_num,
                          sizeof(uj_data.big_num)));

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read big_num_out from OTBN data memory.
  otbn_fi_big_num_out_t uj_output;
  memset(uj_output.big_num, 0, sizeof(uj_output.big_num));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnAppCharBnSelBigNumOut, uj_output.big_num,
                         sizeof(uj_output.big_num)));

  // Read OTBN instruction counter.
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send back to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_big_num_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_bn_wsrr(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_bn_wsrr);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_bn_wsrr, otbn_res_values_wdr);
  const otbn_app_t kOtbnAppCharBnWsrr = OTBN_APP_T_INIT(otbn_char_bn_wsrr);
  static const otbn_addr_t kOtbnAppCharBnWsrrResValuesWDR =
      OTBN_ADDR_T_INIT(otbn_char_bn_wsrr, otbn_res_values_wdr);

  // Load app and write received big_num into DMEM.
  otbn_load_app(kOtbnAppCharBnWsrr);

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Read DMEM
  otbn_fi_data_t uj_output;
  uj_output.res = 0;
  memset(uj_output.data, 0, sizeof(uj_output.data));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnAppCharBnWsrrResValuesWDR, uj_output.data,
                         sizeof(uj_output.data)));
  // Read OTBN instruction counter
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send result & ERR_STATUS to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_data_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_fi_char_bne(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_bne);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_bne, res);
  const otbn_app_t kOtbnAppCharBne = OTBN_APP_T_INIT(otbn_char_bne);
  static const otbn_addr_t kOtbnAppCharBneRes =
      OTBN_ADDR_T_INIT(otbn_char_bne, res);
  otbn_load_app(kOtbnAppCharBne);

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read counter (x1) from OTBN data memory.
  otbn_fi_result_cnt_t uj_output;
  uj_output.result = 0;
  otbn_dmem_read(1, kOtbnAppCharBneRes, &uj_output.result);

  // Read OTBN instruction counter.
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));
  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send back to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_result_cnt_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_dmem_access(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Config for the otbn.fi.char_dmem_access test.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_dmem_access);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_dmem_access, values);
  static const otbn_app_t kOtbnAppCharDmemAccess =
      OTBN_APP_T_INIT(otbn_char_dmem_access);
  static const otbn_addr_t kOtbnVarCharDmemAccessValues =
      OTBN_ADDR_T_INIT(otbn_char_dmem_access, values);

  otbn_load_app(kOtbnAppCharDmemAccess);

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Read DMEM
  otbn_fi_data_t uj_output;
  uj_output.res = 0;
  memset(uj_output.data, 0, sizeof(uj_output.data));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnVarCharDmemAccessValues, uj_output.data,
                         sizeof(uj_output.data)));
  // Read OTBN instruction counter
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Send result & ERR_STATUS to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_data_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_fi_char_dmem_write(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Config for the otbn.fi.char_rf test.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_dmem_write);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_dmem_write, mem);

  static const otbn_app_t kOtbnAppCharDmemWrite =
      OTBN_APP_T_INIT(otbn_char_dmem_write);
  static const otbn_addr_t kOtbnVarCharDmemWriteMem =
      OTBN_ADDR_T_INIT(otbn_char_dmem_write, mem);

  // Init application and load reference values into DMEM.
  otbn_load_app(kOtbnAppCharDmemWrite);
  // FI code target.
  pentest_set_trigger_high();
  asm volatile(NOP30);
  // Unrolled instruction sequence.
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem),
      ref_values[0]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 4),
      ref_values[1]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 8),
      ref_values[2]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 12),
      ref_values[3]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 16),
      ref_values[4]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 20),
      ref_values[5]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 24),
      ref_values[6]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 28),
      ref_values[7]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 32),
      ref_values[8]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 36),
      ref_values[9]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 40),
      ref_values[10]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 44),
      ref_values[11]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 48),
      ref_values[12]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 52),
      ref_values[13]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 56),
      ref_values[14]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 60),
      ref_values[15]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 64),
      ref_values[16]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 68),
      ref_values[17]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 72),
      ref_values[18]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 76),
      ref_values[19]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 80),
      ref_values[20]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 84),
      ref_values[21]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 88),
      ref_values[22]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 92),
      ref_values[23]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 96),
      ref_values[24]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 100),
      ref_values[25]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 104),
      ref_values[26]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 108),
      ref_values[27]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 112),
      ref_values[28]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 116),
      ref_values[29]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 120),
      ref_values[30]);
  mmio_region_write32(
      otbn.base_addr,
      (ptrdiff_t)(OTBN_DMEM_REG_OFFSET + kOtbnVarCharDmemWriteMem + 124),
      ref_values[31]);
  asm volatile(NOP10);
  pentest_set_trigger_low();

  // Execute OTBN application.
  otbn_execute();
  otbn_busy_wait_for_done();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Compare reference values.
  otbn_fi_result_array_t uj_output;
  uint32_t res_values[ARRAYSIZE(ref_values)];
  memset(res_values, 0, sizeof(res_values));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnVarCharDmemWriteMem, res_values,
                         sizeof(res_values)));
  for (size_t it = 0; it < ARRAYSIZE(ref_values); it++) {
    uj_output.result[it] = res_values[it] ^ ref_values[it];
  }

  // Read OTBN instruction counter.
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send result & ERR_STATUS to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_result_array_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_fi_char_hardware_dmem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_hardware_dmem_op_loop);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_hardware_dmem_op_loop, lc);
  const otbn_app_t kOtbnAppCharHardwareDmemOpLoop =
      OTBN_APP_T_INIT(otbn_char_hardware_dmem_op_loop);
  static const otbn_addr_t kOtbnAppCharHardwareDmemOpLoopLC =
      OTBN_ADDR_T_INIT(otbn_char_hardware_dmem_op_loop, lc);
  otbn_load_app(kOtbnAppCharHardwareDmemOpLoop);

  uint32_t loop_counter;

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharHardwareDmemOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_hardware_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_hardware_reg_op_loop);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_hardware_reg_op_loop, lc);
  const otbn_app_t kOtbnAppCharHardwareRegOpLoop =
      OTBN_APP_T_INIT(otbn_char_hardware_reg_op_loop);
  static const otbn_addr_t kOtbnAppCharHardwareRegOpLoopLC =
      OTBN_ADDR_T_INIT(otbn_char_hardware_reg_op_loop, lc);
  otbn_load_app(kOtbnAppCharHardwareRegOpLoop);

  uint32_t loop_counter;

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharHardwareRegOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_jal(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_jal);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_jal, res);
  const otbn_app_t kOtbnAppCharJal = OTBN_APP_T_INIT(otbn_char_jal);
  static const otbn_addr_t kOtbnAppCharJalRes =
      OTBN_ADDR_T_INIT(otbn_char_jal, res);
  otbn_load_app(kOtbnAppCharJal);

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read counter (x1) from OTBN data memory.
  otbn_fi_result_cnt_t uj_output;
  uj_output.result = 0;
  otbn_dmem_read(1, kOtbnAppCharJalRes, &uj_output.result);

  // Read OTBN instruction counter.
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send back to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_result_cnt_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_lw(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_lw);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_lw, mem_in);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_lw, mem_out);
  const otbn_app_t kOtbnAppCharLw = OTBN_APP_T_INIT(otbn_char_lw);
  static const otbn_addr_t kOtbnMemIn = OTBN_ADDR_T_INIT(otbn_char_lw, mem_in);
  static const otbn_addr_t kOtbnMemOut =
      OTBN_ADDR_T_INIT(otbn_char_lw, mem_out);

  // Load app and write reference values into mem_in DMEM.
  otbn_load_app(kOtbnAppCharLw);
  TRY(dif_otbn_dmem_write(&otbn, kOtbnMemIn, ref_values, sizeof(ref_values)));

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Compare reference values. 29 values as we are loading into 29 registers.
  otbn_fi_result_array_t uj_output;
  uint32_t res_values[29];
  memset(res_values, 0, sizeof(res_values));
  memset(uj_output.result, 0, sizeof(uj_output.result));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnMemOut, res_values, sizeof(res_values)));
  for (size_t it = 0; it < 29; it++) {
    uj_output.result[it] = res_values[it] ^ ref_values[it];
  }

  // Read OTBN instruction counter.
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send back to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_result_array_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_mem(ujson_t *uj) {
  // Get the test mode. The test mode only can be set at the beginning of a
  // test.
  if (!char_mem_test_cfg_valid) {
    otbn_fi_mem_cfg_t uj_cfg;
    TRY(ujson_deserialize_otbn_fi_mem_cfg_t(uj, &uj_cfg));
    char_mem_imem = uj_cfg.imem;
    char_mem_dmem = uj_cfg.dmem;
    char_mem_byte_offset = uj_cfg.byte_offset;
    char_mem_num_words = uj_cfg.num_words;
    // Set config to valid.
    char_mem_test_cfg_valid = true;
  }

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Reference values for DMEM and IMEM.
  uint32_t dmem_array_ref[char_mem_num_words];
  uint32_t imem_array_ref[char_mem_num_words];
  if (char_mem_dmem) {
    memset(dmem_array_ref, 0xab, sizeof(dmem_array_ref));
  }
  if (char_mem_imem) {
    memset(imem_array_ref, 0xdf, sizeof(imem_array_ref));
  }

  if (!char_mem_init) {
    if (char_mem_dmem) {
      TRY(dif_otbn_dmem_write(&otbn, char_mem_byte_offset, dmem_array_ref,
                              sizeof(dmem_array_ref)));
    }
    if (char_mem_imem) {
      TRY(dif_otbn_imem_write(&otbn, char_mem_byte_offset, imem_array_ref,
                              sizeof(imem_array_ref)));
    }
    char_mem_init = true;
  }

  // FI code target.
  pentest_set_trigger_high();
  asm volatile(NOP100);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  otbn_fi_mem_t uj_output;
  // Init with all 0 for defaults.
  memset(uj_output.dmem_data, 0, sizeof(uj_output.dmem_data));
  memset(uj_output.dmem_addr, 0, sizeof(uj_output.dmem_addr));
  memset(uj_output.imem_data, 0, sizeof(uj_output.imem_data));
  memset(uj_output.imem_addr, 0, sizeof(uj_output.imem_addr));
  uj_output.res = 0;

  // Check DMEM for data errors.
  size_t fault_pos = 0;
  if (char_mem_dmem) {
    uint32_t dmem_array_res[char_mem_num_words];
    TRY(dif_otbn_dmem_read(&otbn, char_mem_byte_offset, dmem_array_res,
                           sizeof(dmem_array_ref)));
    for (size_t it = 0; it < char_mem_num_words; it++) {
      if (dmem_array_res[it] != dmem_array_ref[it] &&
          fault_pos < ARRAYSIZE(uj_output.dmem_data)) {
        uj_output.dmem_data[fault_pos] = dmem_array_res[it];
        uj_output.dmem_addr[fault_pos] = it;
        fault_pos++;
        // Re-init memory.
        char_mem_init = false;
        uj_output.res = 1;
      }
    }
  }

  // Check IMEM for data errors.
  uint32_t imem_array_res[char_mem_num_words];
  if (char_mem_imem) {
    TRY(dif_otbn_imem_read(&otbn, char_mem_byte_offset, imem_array_res,
                           sizeof(imem_array_ref)));
    fault_pos = 0;
    for (size_t it = 0; it < char_mem_num_words; it++) {
      if (imem_array_res[it] != imem_array_ref[it] &&
          fault_pos < ARRAYSIZE(uj_output.imem_data)) {
        uj_output.imem_data[fault_pos] = imem_array_res[it];
        uj_output.imem_addr[fault_pos] = it;
        fault_pos++;
        // Re-init memory.
        char_mem_init = false;
        uj_output.res = 1;
      }
    }
  }

  // Send result & ERR_STATUS to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_mem_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_fi_char_register_file(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Config for the otbn.fi.char_rf test.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_rf);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_rf, otbn_ref_values);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_rf, otbn_res_values_gpr);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_rf, otbn_res_values_wdr);

  static const otbn_app_t kOtbnAppCharRF = OTBN_APP_T_INIT(otbn_char_rf);
  static const otbn_addr_t kOtbnVarCharRFRefValues =
      OTBN_ADDR_T_INIT(otbn_char_rf, otbn_ref_values);
  static const otbn_addr_t kOtbnVarCharRFResValuesGPR =
      OTBN_ADDR_T_INIT(otbn_char_rf, otbn_res_values_gpr);
  static const otbn_addr_t kOtbnVarCharRFResValuesWDR =
      OTBN_ADDR_T_INIT(otbn_char_rf, otbn_res_values_wdr);

  // Init application and load reference values into DMEM.
  otbn_load_app(kOtbnAppCharRF);
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarCharRFRefValues, ref_values,
                          sizeof(ref_values)));

  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Read GPR RF values from DMEM.
  uint32_t res_values_gpr[29];
  memset(res_values_gpr, 0, sizeof(res_values_gpr));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnVarCharRFResValuesGPR, res_values_gpr,
                         sizeof(res_values_gpr)));

  // Compare GPR RF values to reference values.
  otbn_fi_rf_char_t uj_output;
  memset(uj_output.faulty_gpr, 0, sizeof(uj_output.faulty_gpr));
  uj_output.res = 0;
  for (size_t it = 0; it < ARRAYSIZE(res_values_gpr); it++) {
    if (res_values_gpr[it] != ref_values[it]) {
      uj_output.res = 1;
      // Report reference value XOR faulty value back to also detect faulty
      // values that are 0.
      uj_output.faulty_gpr[it] = res_values_gpr[it] ^ ref_values[it];
    }
  }

  // Read WDR RF values from DMEM.
  uint32_t res_values_wdr[256];
  memset(res_values_wdr, 0, sizeof(res_values_wdr));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnVarCharRFResValuesWDR, res_values_wdr,
                         sizeof(res_values_wdr)));

  // Compare WDR RF values to reference values.
  memset(uj_output.faulty_wdr, 0, sizeof(uj_output.faulty_wdr));
  for (size_t it = 0; it < ARRAYSIZE(res_values_wdr); it++) {
    if (res_values_wdr[it] != ref_values[it % 32]) {
      uj_output.res = 1;
      // Report reference value XOR faulty value back to also detect faulty
      // values that are 0.
      uj_output.faulty_wdr[it] = res_values_wdr[it] ^ ref_values[it % 32];
    }
  }

  // Send result & ERR_STATUS to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_rf_char_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_fi_char_unrolled_dmem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_unrolled_dmem_op_loop);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_unrolled_dmem_op_loop, lc);
  const otbn_app_t kOtbnAppCharUnrolledDmemOpLoop =
      OTBN_APP_T_INIT(otbn_char_unrolled_dmem_op_loop);
  static const otbn_addr_t kOtbnAppCharUnrolledDmemOpLoopLC =
      OTBN_ADDR_T_INIT(otbn_char_unrolled_dmem_op_loop, lc);
  otbn_load_app(kOtbnAppCharUnrolledDmemOpLoop);

  uint32_t loop_counter;

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharUnrolledDmemOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_unrolled_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_char_unrolled_reg_op_loop);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_char_unrolled_reg_op_loop, lc);
  const otbn_app_t kOtbnAppCharUnrolledRegOpLoop =
      OTBN_APP_T_INIT(otbn_char_unrolled_reg_op_loop);
  static const otbn_addr_t kOtbnAppCharUnrolledRegOpLoopLC =
      OTBN_ADDR_T_INIT(otbn_char_unrolled_reg_op_loop, lc);
  otbn_load_app(kOtbnAppCharUnrolledRegOpLoop);

  uint32_t loop_counter;

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharUnrolledRegOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_data));

  // Configure the entropy complex for OTBN. Set the reseed interval to max
  // to avoid a non-constant trigger window.
  TRY(pentest_configure_entropy_source_max_reseed_interval());

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  pentest_init(kPentestTriggerSourceOtbn,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralAes | kPentestPeripheralHmac |
                   kPentestPeripheralKmac | kPentestPeripheralOtbn);

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Init the OTBN core.
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler();

  // Configure the CPU for the pentest.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_data.icache_disable, uj_data.dummy_instr_disable,
      uj_data.enable_jittery_clock, uj_data.enable_sram_readback,
      &uj_output.clock_jitter_locked, &uj_output.clock_jitter_en,
      &uj_output.sram_main_readback_locked, &uj_output.sram_ret_readback_locked,
      &uj_output.sram_main_readback_en, &uj_output.sram_ret_readback_en));
  ;

  // The load integrity, key sideloading, and char_mem tests get initialized at
  // the first run.
  load_integrity_init = false;
  key_sideloading_init = false;
  char_mem_init = false;
  char_mem_test_cfg_valid = false;

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_fi_init_keymgr(ujson_t *uj) {
  dif_kmac_t kmac;
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  TRY(dif_keymgr_init(mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR),
                      &keymgr));
  TRY(keymgr_testutils_initialize(&keymgr, &kmac));

  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParamsOTBNFI;
  sideload_params.dest = kDifKeymgrVersionedKeyDestOtbn;
  TRY(keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  return OK_STATUS();
}

status_t handle_otbn_fi_key_sideload(ujson_t *uj) {
  TRY(dif_otbn_set_ctrl_software_errs_fatal(&otbn, /*enable=*/false));
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  if (!key_sideloading_init) {
    // Setup keymanager for sideloading key into OTBN.
    otbn_load_app(kOtbnAppKeySideload);
    // Get reference keys.
    otbn_execute();
    otbn_busy_wait_for_done();

    otbn_dmem_read(1, kOtbnAppKeySideloadks0l, &key_share_0_l_ref);
    otbn_dmem_read(1, kOtbnAppKeySideloadks0h, &key_share_0_h_ref);
    otbn_dmem_read(1, kOtbnAppKeySideloadks1l, &key_share_1_l_ref);
    otbn_dmem_read(1, kOtbnAppKeySideloadks1h, &key_share_1_h_ref);

    key_sideloading_init = true;
  }

  // FI code target.
  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read loop counter from OTBN data memory.
  uint32_t key_share_0_l, key_share_0_h;
  uint32_t key_share_1_l, key_share_1_h;
  otbn_dmem_read(1, kOtbnAppKeySideloadks0l, &key_share_0_l);
  otbn_dmem_read(1, kOtbnAppKeySideloadks0h, &key_share_0_h);
  otbn_dmem_read(1, kOtbnAppKeySideloadks1l, &key_share_1_l);
  otbn_dmem_read(1, kOtbnAppKeySideloadks1h, &key_share_1_h);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  otbn_fi_keys_t uj_output;
  uj_output.keys[0] = key_share_0_l;
  uj_output.keys[1] = key_share_0_h;
  uj_output.keys[2] = key_share_1_l;
  uj_output.keys[3] = key_share_1_h;

  uj_output.res = 0;
  if ((key_share_0_l != key_share_0_l_ref) ||
      (key_share_0_h != key_share_0_h_ref) ||
      (key_share_1_l != key_share_1_l_ref) ||
      (key_share_1_h != key_share_1_h_ref)) {
    uj_output.res = 1;
  }

  // Send result & ERR_STATUS to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_keys_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_load_integrity(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  if (!load_integrity_init) {
    // Load the OTBN app and read the load checksum without FI to retrieve
    // reference value.
    clear_otbn_load_checksum();
    otbn_load_app(kOtbnAppLoadIntegrity);
    read_otbn_load_checksum(&load_checksum_ref);
    clear_otbn_load_checksum();

    load_integrity_init = true;
  }

  // FI code target.
  pentest_set_trigger_high();
  otbn_load_app(kOtbnAppLoadIntegrity);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read back checksum.
  uint32_t load_checksum;
  read_otbn_load_checksum(&load_checksum);
  clear_otbn_load_checksum();

  // Read loop counter from OTBN data memory.
  uint32_t ref_val1, ref_val2, ref_val3;
  otbn_dmem_read(1, kOtbnAppLoadIntegrityRefVal1, &ref_val1);
  otbn_dmem_read(1, kOtbnAppLoadIntegrityRefVal2, &ref_val2);
  otbn_dmem_read(1, kOtbnAppLoadIntegrityRefVal3, &ref_val3);

  // Check if DMEM is corrupted.
  bool dmem_corrupted = false;
  if ((ref_val1 != 0x1BADB002) || (ref_val2 != 0x8BADF00D) ||
      (ref_val3 != 0xA5A5A5A5)) {
    dmem_corrupted = true;
  }

  // If DMEM is corrupted and the checksum is still correct, we achieved the
  // attack goal.
  uint32_t res = 0;
  if ((load_checksum_ref == load_checksum) && dmem_corrupted) {
    res = 1;
  }

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send result & ERR_STATUS to host.
  otbn_fi_result_t uj_output;
  uj_output.result = res;
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_pc(ujson_t *uj) {
  // Get OTBN program counter from host.
  otbn_fi_pc_t uj_data;
  TRY(ujson_deserialize_otbn_fi_pc_t(uj, &uj_data));

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize OTBN app, load it, and get interface to OTBN data memory.
  OTBN_DECLARE_APP_SYMBOLS(otbn_pc);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_pc, pc);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_pc, pc_out);
  const otbn_app_t kOtbnAppPc = OTBN_APP_T_INIT(otbn_pc);
  static const otbn_addr_t kOtbnPc = OTBN_ADDR_T_INIT(otbn_pc, pc);
  static const otbn_addr_t kOtbnPcOut = OTBN_ADDR_T_INIT(otbn_pc, pc_out);
  dif_otbn_status_t otbn_status;

  // Load app.
  otbn_load_app(kOtbnAppPc);

  // FI code target.
  pentest_set_trigger_high();
  TRY(dif_otbn_dmem_write(&otbn, kOtbnPc, &uj_data.pc, sizeof(uj_data.pc)));
  otbn_execute();
  // Wait until is started before deasserting the trigger.
  bool is_running = false;
  while (!is_running) {
    TRY(dif_otbn_get_status(&otbn, &otbn_status));
    if (otbn_status != kDifOtbnStatusIdle) {
      is_running = true;
    }
  }
  pentest_set_trigger_low();
  otbn_busy_wait_for_done();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read pc_out from OTBN data memory.
  otbn_fi_pc_out_t uj_output;
  TRY(dif_otbn_dmem_read(&otbn, kOtbnPcOut, &uj_output.pc_otbn,
                         sizeof(uj_output.pc_otbn)));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnPc, &uj_output.pc_dmem,
                         sizeof(uj_output.pc_dmem)));

  // Read OTBN instruction counter.
  TRY(dif_otbn_get_insn_cnt(&otbn, &uj_output.insn_cnt));

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_otbn;
  read_otbn_err_bits(&err_otbn);

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send back to host.
  uj_output.err_otbn = err_otbn;
  uj_output.err_ibx = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_otbn_fi_pc_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi(ujson_t *uj) {
  otbn_fi_subcommand_t cmd;
  TRY(ujson_deserialize_otbn_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kOtbnFiSubcommandCharBeq:
      return handle_otbn_fi_char_beq(uj);
    case kOtbnFiSubcommandCharBnRshi:
      return handle_otbn_fi_char_bn_rshi(uj);
    case kOtbnFiSubcommandCharBnSel:
      return handle_otbn_fi_char_bn_sel(uj);
    case kOtbnFiSubcommandCharBnWsrr:
      return handle_otbn_fi_char_bn_wsrr(uj);
    case kOtbnFiSubcommandCharBne:
      return handle_otbn_fi_char_bne(uj);
    case kOtbnFiSubcommandCharDmemAccess:
      return handle_otbn_fi_char_dmem_access(uj);
    case kOtbnFiSubcommandCharDmemWrite:
      return handle_otbn_fi_char_dmem_write(uj);
    case kOtbnFiSubcommandCharHardwareDmemOpLoop:
      return handle_otbn_fi_char_hardware_dmem_op_loop(uj);
    case kOtbnFiSubcommandCharHardwareRegOpLoop:
      return handle_otbn_fi_char_hardware_reg_op_loop(uj);
    case kOtbnFiSubcommandCharJal:
      return handle_otbn_fi_char_jal(uj);
    case kOtbnFiSubcommandCharLw:
      return handle_otbn_fi_char_lw(uj);
    case kOtbnFiSubcommandCharMem:
      return handle_otbn_fi_char_mem(uj);
    case kOtbnFiSubcommandCharRF:
      return handle_otbn_fi_char_register_file(uj);
    case kOtbnFiSubcommandCharUnrolledDmemOpLoop:
      return handle_otbn_fi_char_unrolled_dmem_op_loop(uj);
    case kOtbnFiSubcommandCharUnrolledRegOpLoop:
      return handle_otbn_fi_char_unrolled_reg_op_loop(uj);
    case kOtbnFiSubcommandInit:
      return handle_otbn_fi_init(uj);
    case kOtbnFiSubcommandInitKeyMgr:
      return handle_otbn_fi_init_keymgr(uj);
    case kOtbnFiSubcommandKeySideload:
      return handle_otbn_fi_key_sideload(uj);
    case kOtbnFiSubcommandLoadIntegrity:
      return handle_otbn_fi_load_integrity(uj);
    case kOtbnFiSubcommandPC:
      return handle_otbn_fi_pc(uj);
    default:
      LOG_ERROR("Unrecognized OTBN FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
