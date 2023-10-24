// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_UTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_UTILS_H_

#include <stdbool.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"

/**
 * Wait until a condition is true.
 *
 * @param cond: an expression that can be repeated tested for.
 * @param timeout_usec: timeout in microseconds.
 *
 * In DV, this function will simply spin since the DV environment can do
 * backdoor writes to make the condition true. On real device, this will wait
 * for host to send ujson message. The condition is check after each command.
 */
#define OTTF_WAIT_FOR(cond, timeout_usec)                                  \
  do {                                                                     \
    if (kDeviceType != kDeviceSimDV) {                                     \
      ujson_t uj = ujson_ottf_console();                                   \
      const ibex_timeout_t timeout_ = ibex_timeout_init(timeout_usec);     \
      test_command_t command;                                              \
      LOG_INFO("SiVal: waiting for commands");                             \
      while (!(cond)) {                                                    \
        CHECK(!ibex_timeout_check(&timeout_),                              \
              "Timed out after %d usec waiting for " #cond, timeout_usec); \
        /* FIXME: what to do on error? */                                  \
        CHECK_STATUS_OK(ujson_deserialize_test_command_t(&uj, &command));  \
        CHECK_STATUS_OK(ujson_ottf_dispatch(&uj, command));                \
      }                                                                    \
    } else {                                                               \
      IBEX_SPIN_FOR(cond, timeout_usec);                                   \
    }                                                                      \
  } while (0)

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_UTILS_H_
