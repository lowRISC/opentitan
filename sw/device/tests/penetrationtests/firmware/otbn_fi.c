// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/otbn_fi.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/firmware/sca_lib.h"
#include "sw/device/tests/penetrationtests/json/otbn_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"

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
const otbn_app_t kOtbnAppLoadIntegrity = OTBN_APP_T_INIT(otbn_load_integrity);
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

// Key diversification data for testing
static const keymgr_diversification_t kTestDiversification = {
    .salt =
        {
            0x00112233,
            0x44556677,
            0x8899aabb,
            0xccddeeff,
            0x00010203,
            0x04050607,
            0x08090a0b,
            0x0c0d0e0f,
        },
    .version = 0x9,
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

  return OK_STATUS(0);
}

/**
 * Read the error bits of the OTBN accelerator.
 *
 * @returns Error bits.
 */
status_t read_otbn_err_bits(dif_otbn_err_bits_t *err_bits) {
  dif_otbn_t otbn;
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  TRY(dif_otbn_get_err_bits(&otbn, err_bits));
  return OK_STATUS(0);
}

/**
 * Read the OTBN load checksum.
 *
 * @returns Load checksum.
 */
status_t read_otbn_load_checksum(uint32_t *checksum) {
  dif_otbn_t otbn;
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  TRY(dif_otbn_get_load_checksum(&otbn, checksum));
  return OK_STATUS(0);
}

/**
 * Clear the OTBN load checksum.
 */
status_t clear_otbn_load_checksum(void) {
  dif_otbn_t otbn;
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  TRY(dif_otbn_clear_load_checksum(&otbn));
  return OK_STATUS(0);
}

/**
 * otbn.fi.key_sideload command handler.
 *
 * Injects a fault when a key is sideloaded from the key manager into OTBN.
 *
 * Faults are injected during the trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_key_sideload(ujson_t *uj) {
  if (!key_sideloading_init) {
    // Setup keymanager for sideloading key into OTBN.
    otbn_load_app(kOtbnAppKeySideload);
    key_sideloading_init = true;
  }

  // FI code target.
  sca_set_trigger_high();
  status_t keymgr_res = keymgr_generate_key_otbn(kTestDiversification);
  otbn_execute();
  otbn_busy_wait_for_done();
  sca_set_trigger_low();

  // Read loop counter from OTBN data memory.
  uint32_t key_share_0_l, key_share_0_l_ref;
  uint32_t key_share_0_h, key_share_0_h_ref;
  uint32_t key_share_1_l, key_share_1_l_ref;
  uint32_t key_share_1_h, key_share_1_h_ref;
  otbn_dmem_read(1, kOtbnAppKeySideloadks0l, &key_share_0_l);
  otbn_dmem_read(1, kOtbnAppKeySideloadks0h, &key_share_0_h);
  otbn_dmem_read(1, kOtbnAppKeySideloadks1l, &key_share_1_l);
  otbn_dmem_read(1, kOtbnAppKeySideloadks1h, &key_share_1_h);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Set error value to 1 if key sideloading failed.
  uint32_t res = 0;
  if (keymgr_res.value != kHardenedBoolTrue) {
    res = 1;
  }

  // Read key again and compare.
  otbn_load_app(kOtbnAppKeySideload);
  keymgr_res = keymgr_generate_key_otbn(kTestDiversification);
  if (keymgr_res.value != kHardenedBoolTrue) {
    return ABORTED();
  }
  otbn_execute();
  otbn_busy_wait_for_done();

  otbn_dmem_read(1, kOtbnAppKeySideloadks0l, &key_share_0_l_ref);
  otbn_dmem_read(1, kOtbnAppKeySideloadks0h, &key_share_0_h_ref);
  otbn_dmem_read(1, kOtbnAppKeySideloadks1l, &key_share_1_l_ref);
  otbn_dmem_read(1, kOtbnAppKeySideloadks1h, &key_share_1_h_ref);

  if ((key_share_0_l != key_share_0_l_ref) ||
      (key_share_0_h != key_share_0_h_ref) ||
      (key_share_1_l != key_share_1_l_ref) ||
      (key_share_1_h != key_share_1_h_ref)) {
    res |= 2;
  }

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send result & ERR_STATUS to host.
  otbn_fi_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = err_bits;
  RESP_OK(ujson_serialize_otbn_fi_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * otbn.fi.load_integrity command handler.
 *
 * Tests, whether a fault during loading the OTBN app can manipulate data in
 * DMEM without changing the CRC-32 checksum that is used to check the
 * integrity of the DMEM and IMEM.
 *
 * As the OTBN app itself is not the target of this FI analysis, it only
 * consists of NOPs. The DMEM is initialized with reference values that
 * are checked.
 *
 * Faults are injected during the trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_load_integrity(ujson_t *uj) {
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
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send result & ERR_STATUS to host.
  otbn_fi_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = err_bits;
  RESP_OK(ujson_serialize_otbn_fi_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * otbn.fi.char.hardware.dmem.op.loop command handler.
 *
 * This FI penetration tests executes the following instructions on OTBN:
 * - Initialize register x3=0
 * - Perform 10000 x3 = x3 + 1 additions using hardware loop instructions.
 *   Load loop counter from memory and write back after increment.
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_char_hardware_dmem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  reg_alerts = sca_get_triggered_alerts();

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharHardwareDmemOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = err_bits;
  uj_output.alerts_1 = reg_alerts.alerts_1;
  uj_output.alerts_2 = reg_alerts.alerts_2;
  uj_output.alerts_3 = reg_alerts.alerts_3;
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * otbn.fi.char.hardware.reg.op.loop command handler.
 *
 * This FI penetration tests executes the following instructions on OTBN:
 * - Initialize register x3=0
 * - Perform 10000 x3 = x3 + 1 additions using hardware loop instructions
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_char_hardware_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  reg_alerts = sca_get_triggered_alerts();

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharHardwareRegOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = err_bits;
  uj_output.alerts_1 = reg_alerts.alerts_1;
  uj_output.alerts_2 = reg_alerts.alerts_2;
  uj_output.alerts_3 = reg_alerts.alerts_3;
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * otbn.fi.char.unrolled.dmem.op.loop command handler.
 *
 * This FI penetration tests executes the following instructions on OTBN:
 * - Perform 100 times:
 *  - Load loop counter from memory
 *  - Increment loop counter
 *  - Store back to memory
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_char_unrolled_dmem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  reg_alerts = sca_get_triggered_alerts();

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharUnrolledDmemOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = err_bits;
  uj_output.alerts_1 = reg_alerts.alerts_1;
  uj_output.alerts_2 = reg_alerts.alerts_2;
  uj_output.alerts_3 = reg_alerts.alerts_3;
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * otbn.char.unrolled.reg.op.loop command handler.
 *
 * This FI penetration tests executes the following instructions on OTBN:
 * - Initialize register x2=0
 * - Perform 100 x2 = x2 + 1 additions
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_char_unrolled_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  reg_alerts = sca_get_triggered_alerts();

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharUnrolledRegOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Clear OTBN memory.
  TRY(clear_otbn());

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = err_bits;
  uj_output.alerts_1 = reg_alerts.alerts_1;
  uj_output.alerts_2 = reg_alerts.alerts_2;
  uj_output.alerts_3 = reg_alerts.alerts_3;
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * Initializes the key manager.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_init_keymgr(ujson_t *uj) {
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  TRY(keymgr_testutils_startup(&keymgr, &kmac));
  TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
  TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerRootKeyParams));
  TRY(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerRootKey));

  return OK_STATUS(0);
}

/**
 * Initializes the OTBN FI test.
 *
 * Setup the trigger and alert handler. Disable dummy instructions and the
 * iCache.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_init(ujson_t *uj) {
  status_t err = entropy_testutils_auto_mode_init();
  sca_select_trigger_type(kScaTriggerTypeSw);
  sca_init(kScaTriggerSourceOtbn,
           kScaPeripheralIoDiv4 | kScaPeripheralEdn | kScaPeripheralCsrng |
               kScaPeripheralEntropy | kScaPeripheralAes | kScaPeripheralHmac |
               kScaPeripheralKmac | kScaPeripheralOtbn);

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  sca_configure_alert_handler();

  // Disable the instruction cache and dummy instructions for FI attacks.
  sca_configure_cpu();

  // The load integrity & key sideloading tests get initialized at the first
  // run.
  load_integrity_init = false;
  key_sideloading_init = false;

  // Read the device ID and return it back to the host.
  TRY(sca_read_device_id(uj));

  return err;
}

/**
 * OTBN FI command handler.
 *
 * Command handler for the OTBN FI command.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi(ujson_t *uj) {
  otbn_fi_subcommand_t cmd;
  TRY(ujson_deserialize_otbn_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kOtbnFiSubcommandInitKeyMgr:
      return handle_otbn_fi_init_keymgr(uj);
    case kOtbnFiSubcommandInit:
      return handle_otbn_fi_init(uj);
    case kOtbnFiSubcommandCharUnrolledRegOpLoop:
      return handle_otbn_fi_char_unrolled_reg_op_loop(uj);
    case kOtbnFiSubcommandCharUnrolledDmemOpLoop:
      return handle_otbn_fi_char_unrolled_dmem_op_loop(uj);
    case kOtbnFiSubcommandCharHardwareRegOpLoop:
      return handle_otbn_fi_char_hardware_reg_op_loop(uj);
    case kOtbnFiSubcommandCharHardwareDmemOpLoop:
      return handle_otbn_fi_char_hardware_dmem_op_loop(uj);
    case kOtbnFiSubcommandLoadIntegrity:
      return handle_otbn_fi_load_integrity(uj);
    case kOtbnFiSubcommandKeySideload:
      return handle_otbn_fi_key_sideload(uj);
    default:
      LOG_ERROR("Unrecognized OTBN FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
