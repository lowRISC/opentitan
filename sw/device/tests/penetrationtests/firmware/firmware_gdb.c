// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
//  CI ISSUES                                                                 //
//                                                                            //
//  If this is a failing test, please also adapt/raise an issue/contact for   //
//  the tests in //sw/host/penetrationtests/python/fi/gdb_testing.            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#include <stdbool.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"

// Include commands
#include "sw/device/tests/penetrationtests/json/gdb_commands.h"
#include "sw/device/tests/penetrationtests/json/pentest_lib_commands.h"

// This file contains some secure coding styles and guidelines which is used for
// unit testing of fault simulation.

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

// Markers in the dis file to be able to trace certain functions
#define PENTEST_MARKER_LABEL(name) asm volatile(#name ":" ::: "memory")

status_t handle_gdb_init(ujson_t *uj) {
  // Configure the device.
  pentest_setup_device(uj, true, false);

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralKmac);

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  return OK_STATUS();
}

// This is an example function setting its input variable to true and assuming
// its input is false. The function is coded in a secure style. The function
// should return a status_t signifying whether or not the function executed
// correctly. The status will be checked by a HARDENED_TRY. In this example, the
// status out is put through a launder32 function in order to have the compiler
// not optimize the return (this is not needed in case the return logic is more
// complex).
OT_NOINLINE status_t set_to_true_helper(bool *result) {
  if (*result) {
    return OTCRYPTO_BAD_ARGS;
  }
  *result = true;
  // We add a HARDENED_CHECK_EQ in order to verify the value was set correctly.
  HARDENED_CHECK_EQ(*result, launder32(true));
  // Since the input is a pointer, an instruction skip can skip the assignment
  // of true in the memory but leave it correctly set in the register. We can
  // either force a cehck on a reload of the value in memory in the
  // HARDENED_CHECK_EQ or we more a redundant setting of the value.
  *result = launder32(true);

  return (status_t){.value = (int)launder32(kHardenedBoolTrue)};
}

// The secure guideline check for the calling of a function.
status_t handle_gdb_try_test(ujson_t *uj) {
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  gdb_out_t uj_output;
  // Start a secure execution by setting the status to an invalid value.
  uj_output.status = launder32(kHardenedBoolFalse);

  // The attacker's goal is to leave result to false.
  uj_output.result = false;

  // Trigger window.
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GDB_TRY_START);
  pentest_set_trigger_high();

  // Call a secure function in the HARDENED_TRY macro.
  HARDENED_TRY(set_to_true_helper(&uj_output.result));
  // Once the secure execution is finished, set the status to ok (here 0, but a
  // magic value is preferred).
  uj_output.status = 0;

  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GDB_TRY_END);

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_gdb_out_t, uj, &uj_output);
  return OK_STATUS();
}

// Helper returning a legitimate error status for testing the HARDENED_TRY
// error path. Hardened internally so faults specifically probe HARDENED_TRY in
// the caller rather than the helper itself.
OT_NOINLINE status_t return_bad_status_helper(void) {
  uint32_t err = launder32((uint32_t)OTCRYPTO_BAD_ARGS.value);
  HARDENED_CHECK_EQ(err, (uint32_t)OTCRYPTO_BAD_ARGS.value);
  return (status_t){.value = (int32_t)err};
}

// Multi-call wrapper so the compiler exercises tail-merging across multiple
// HARDENED_TRY sites (matching real cryptolib functions).
OT_NOINLINE status_t try_err_inner(bool *result) {
  HARDENED_TRY(return_bad_status_helper());
  HARDENED_TRY(set_to_true_helper(result));
  return OTCRYPTO_OK;
}

// Adversarial bad-status test for HARDENED_TRY: the first HARDENED_TRY callee
// returns OTCRYPTO_BAD_ARGS and the attacker attempts to bypass HARDENED_TRY so
// execution falls through to `set_to_true_helper`.
status_t handle_gdb_try_err_test(ujson_t *uj) {
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  gdb_out_t uj_output;
  // Initialize to an error status and false result. The attacker's goal is to
  // bypass the failing HARDENED_TRY so result becomes true or status becomes
  // OTCRYPTO_OK (kHardenedBoolTrue).
  uj_output.status = (uint32_t)OTCRYPTO_RECOV_ERR.value;
  uj_output.result = false;

  // Trigger window.
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GDB_TRY_ERR_START);
  pentest_set_trigger_high();

  status_t res = try_err_inner(&uj_output.result);
  uj_output.status = (uint32_t)res.value;

  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GDB_TRY_ERR_END);

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_gdb_out_t, uj, &uj_output);
  return OK_STATUS();
}

// The secure guideline of implementing a switch case.
status_t handle_gdb_switch_test(ujson_t *uj) {
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  gdb_out_t uj_output;
  // Start a secure execution by setting the status to an invalid value.
  uj_output.status = launder32(kHardenedBoolFalse);
  // The attacker's goal is to set the result to false.
  uj_output.result = true;

  uint32_t switch_case = kHardenedBoolTrue;

  // Trigger window.
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GDB_SWITCH_START);
  pentest_set_trigger_high();

  // Start a redundant value to verify the correct switch case was followed.
  // Use launder to block optimization.
  hardened_bool_t switch_case_check = launder32(0);
  switch (switch_case) {
    // Cases best use magic values.
    case kHardenedBoolTrue:
      // Verify the correct switch case was followed by ORing the case to the
      // redundant value. This also would detect the case more than one case was
      // taken.
      switch_case_check = launder32(switch_case_check) | kHardenedBoolTrue;
      break;
    case kHardenedBoolFalse:
      // The desired case for the attacker.
      uj_output.result = false;
      switch_case_check = launder32(switch_case_check) | kHardenedBoolFalse;
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }
  // Verify the correct case was followed via a HARDENED_CHECK_EQ.
  HARDENED_CHECK_EQ(launder32(switch_case_check), switch_case);
  // Once the secure execution is finished, set the status to ok (here 0, but a
  // magic value is preferred).
  uj_output.status = 0;

  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GDB_SWITCH_END);

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_gdb_out_t, uj, &uj_output);
  return OK_STATUS();
}

// The secure guideline to make an if loop.
status_t handle_gdb_if_test(ujson_t *uj) {
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  gdb_out_t uj_output;
  // Start a secure execution by setting the status to an invalid value.
  uj_output.status = launder32(kHardenedBoolFalse);
  // The attacker's goal is to set the result to false.
  uj_output.result = true;

  uint32_t if_check = kHardenedBoolTrue;

  // Trigger window.
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GDB_IF_START);
  pentest_set_trigger_high();

  // Cases best use magic values.
  if (launder32(if_check) == kHardenedBoolFalse) {
    // In an if loop, check the case again via a HARDENED_CHECK_EQ.
    HARDENED_CHECK_EQ(if_check, kHardenedBoolTrue);
    // The desired state for the attacker.
    uj_output.result = false;
  }
  // Once the secure execution is finished, set the status to ok (here 0, but a
  // magic value is preferred).
  uj_output.status = 0;

  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GDB_IF_END);

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_gdb_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_gdb(ujson_t *uj) {
  while (true) {
    gdb_subcommand_t cmd;
    TRY(ujson_deserialize_gdb_subcommand_t(uj, &cmd));
    switch (cmd) {
      case kGdbSubcommandInit:
        RESP_ERR(uj, handle_gdb_init(uj));
        break;
      case kGdbSubcommandTry:
        RESP_ERR(uj, handle_gdb_try_test(uj));
        break;
      case kGdbSubcommandTryErr:
        RESP_ERR(uj, handle_gdb_try_err_test(uj));
        break;
      case kGdbSubcommandSwitch:
        RESP_ERR(uj, handle_gdb_switch_test(uj));
        break;
      case kGdbSubcommandIf:
        RESP_ERR(uj, handle_gdb_if_test(uj));
        break;
      default:
        LOG_ERROR("Unrecognized GDB test subcommand: %d", cmd);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));
  ujson_t uj = ujson_ottf_console();
  return status_ok(handle_gdb(&uj));
}
