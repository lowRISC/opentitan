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
#include "sw/device/sca/lib/sca.h"
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

uint32_t key_share_0_l_ref, key_share_0_h_ref;
uint32_t key_share_1_l_ref, key_share_1_h_ref;

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

status_t handle_otbn_fi_char_hardware_dmem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  sca_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_hardware_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  sca_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_unrolled_dmem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  sca_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_char_unrolled_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  sca_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_init(ujson_t *uj) {
  // Configure the entropy complex for OTBN. Set the reseed interval to max
  // to avoid a non-constant trigger window.
  TRY(pentest_configure_entropy_source_max_reseed_interval());

  sca_select_trigger_type(kScaTriggerTypeSw);
  sca_init(kScaTriggerSourceOtbn,
           kScaPeripheralIoDiv4 | kScaPeripheralEdn | kScaPeripheralCsrng |
               kScaPeripheralEntropy | kScaPeripheralAes | kScaPeripheralHmac |
               kScaPeripheralKmac | kScaPeripheralOtbn);

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Init the OTBN core.
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler();

  // Disable the instruction cache and dummy instructions for FI attacks.
  pentest_configure_cpu();

  // The load integrity & key sideloading tests get initialized at the first
  // run.
  load_integrity_init = false;
  key_sideloading_init = false;

  // Read device ID and return to host.
  penetrationtest_device_id_t uj_output;
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

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
  sca_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  sca_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  sca_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_otbn_fi_keys_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi_load_integrity(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  sca_set_trigger_high();
  otbn_load_app(kOtbnAppLoadIntegrity);
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_otbn_fi_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_fi(ujson_t *uj) {
  otbn_fi_subcommand_t cmd;
  TRY(ujson_deserialize_otbn_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kOtbnFiSubcommandCharHardwareDmemOpLoop:
      return handle_otbn_fi_char_hardware_dmem_op_loop(uj);
    case kOtbnFiSubcommandCharHardwareRegOpLoop:
      return handle_otbn_fi_char_hardware_reg_op_loop(uj);
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
    default:
      LOG_ERROR("Unrecognized OTBN FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
