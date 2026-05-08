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
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
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
  if (if_check == kHardenedBoolFalse) {
    // In an if loop, check the case again via a HARDENED_CHECK_EQ.
    HARDENED_CHECK_EQ(launder32(if_check), kHardenedBoolTrue);
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
  CHECK_STATUS_OK(entropy_complex_init());
  ujson_t uj = ujson_ottf_console();
  return status_ok(handle_gdb(&uj));
}
