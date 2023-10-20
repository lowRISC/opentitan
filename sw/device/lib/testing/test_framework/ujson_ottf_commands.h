// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_UJSON_OTTF_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_UJSON_OTTF_COMMANDS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/ujson/ujson.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Handles basic memory commands known to the OTTF ujson framework.
 *
 * For unrecognized command codes, no response is sent back to the requester.
 * This function returns a status with code `kUnimplemented`, and the caller
 * chooses whether to send an error response or to forward the command code to
 * some other handling routine.
 *
 * @param uj A ujson IO context.
 * @param command The identifier for the command that was received.
 * @return The status result of the operation, where kOk means the command's
 *         operation completed, kUnimplemented means the command ID is unknown
 *         to the function and may belong to a different space, and any other
 *         status represents an error.
 */
status_t ujson_ottf_dispatch(ujson_t *uj, test_command_t command);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_UJSON_OTTF_COMMANDS_H_
