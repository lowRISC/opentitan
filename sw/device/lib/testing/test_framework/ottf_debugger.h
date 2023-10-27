// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_DEBUGGER_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_DEBUGGER_H_

#include <stdbool.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

/**
 * Put the OTTF into debugger mode where it can receive commands from the host.
 *
 * @param uj A ujson IO context. Pass NULL to create a temporary one.
 * @return The status result of the operation, where kOk means that the host
 *         asked to exit the debugger loop, and any other status represents an
 *         error that occurred during the handling of a command.
 */
status_t ottf_debugger_loop(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_DEBUGGER_H_
