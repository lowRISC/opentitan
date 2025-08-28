// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_TYPES_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_TYPES_H_

#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

typedef struct ottf_console ottf_console_t;

/**
 * Flow control state.
 */
typedef enum ottf_console_flow_control {
  /** No flow control enabled. */
  kOttfConsoleFlowControlNone = 0,
  /** Automatically determine the next flow control state. */
  kOttfConsoleFlowControlAuto = 1,
  /**
   * Flow control is in the `Resume` state (safe to receive).
   * This is also the ASCII code for `XON`.
   */
  kOttfConsoleFlowControlResume = 17,
  /**
   * Flow control is in the `Pause` state (risk of overrun).
   * This is also the ASCII code for `XOFF`.
   */
  kOttfConsoleFlowControlPause = 19,
} ottf_console_flow_control_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_TYPES_H_
