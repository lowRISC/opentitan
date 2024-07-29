// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/otbn_fi.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/json/otbn_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"

/**
 * Reat the error bits of the OTBN accelerator.
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

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharHardwareDmemOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = err_bits;
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

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharHardwareRegOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = err_bits;
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

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharUnrolledDmemOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = err_bits;
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

  // Read loop counter from OTBN data memory.
  otbn_dmem_read(1, kOtbnAppCharUnrolledRegOpLoopLC, &loop_counter);

  // Read ERR_STATUS register from OTBN.
  dif_otbn_err_bits_t err_bits;
  read_otbn_err_bits(&err_bits);

  // Send loop counter & ERR_STATUS to host.
  otbn_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = err_bits;
  RESP_OK(ujson_serialize_otbn_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * Initializes the SCA trigger.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_fi_init_trigger(ujson_t *uj) {
  status_t err = entropy_testutils_auto_mode_init();
  sca_select_trigger_type(kScaTriggerTypeSw);
  sca_init(kScaTriggerSourceOtbn, kScaPeripheralEntropy | kScaPeripheralIoDiv4 |
                                      kScaPeripheralOtbn | kScaPeripheralCsrng |
                                      kScaPeripheralEdn | kScaPeripheralHmac);
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
    case kOtbnFiSubcommandInitTrigger:
      return handle_otbn_fi_init_trigger(uj);
    case kOtbnFiSubcommandCharUnrolledRegOpLoop:
      return handle_otbn_fi_char_unrolled_reg_op_loop(uj);
    case kOtbnFiSubcommandCharUnrolledDmemOpLoop:
      return handle_otbn_fi_char_unrolled_dmem_op_loop(uj);
    case kOtbnFiSubcommandCharHardwareRegOpLoop:
      return handle_otbn_fi_char_hardware_reg_op_loop(uj);
    case kOtbnFiSubcommandCharHardwareDmemOpLoop:
      return handle_otbn_fi_char_hardware_dmem_op_loop(uj);
    default:
      LOG_ERROR("Unrecognized OTBN FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
