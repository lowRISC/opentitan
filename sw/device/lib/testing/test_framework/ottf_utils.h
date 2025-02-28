// Copyright lowRISC contributors (OpenTitan project).
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
 * NOTE: all variables which appear in `cond` should be declared by
 * `OTTF_BACKDOOR_VAR` to prevent compiler optimization that could result
 * in unexpected behaviours.
 *
 * In DV, this function will simply spin since the DV environment can do
 * backdoor writes to make the condition true. On real device, this will wait
 * for host to send ujson message. The condition is check after each command.
 */
#define OTTF_WAIT_FOR(cond, timeout_usec)                                     \
  do {                                                                        \
    if (kDeviceType != kDeviceSimDV) {                                        \
      ujson_t uj = ujson_ottf_console();                                      \
      const ibex_timeout_t timeout_ = ibex_timeout_init(timeout_usec);        \
      test_command_t command;                                                 \
      LOG_INFO("SiVal: waiting for commands");                                \
      while (!(cond)) {                                                       \
        CHECK(!ibex_timeout_check(&timeout_),                                 \
              "Timed out after %d usec waiting for " #cond, timeout_usec);    \
        /* FIXME: what to do on error? */                                     \
        CHECK_STATUS_OK(                                                      \
            UJSON_WITH_CRC(ujson_deserialize_test_command_t, &uj, &command)); \
        CHECK_STATUS_OK(ujson_ottf_dispatch(&uj, command));                   \
      }                                                                       \
    } else {                                                                  \
      IBEX_SPIN_FOR(cond, timeout_usec);                                      \
    }                                                                         \
  } while (0)

/**
 * Declare a variable which can be used with `OTTF_WAIT_FOR`.
 *
 * This macro guarantees the following:
 * - This variable can be used within the condition of `OTTF_WAIT_FOR` and
 *   the compiler will not optimize the condition thinking that the variable
 *   is not modified, *even* if the program never writes to it.
 * - This variable will have an associated symbol in the final ELF binary.
 *
 * NOTE: this macro guarantees that the variable works in all non-DV
 * environments but may not work in DV.
 *
 * Example:
 * ```c
 * OTTF_BACKDOOR_VAR bool sival_is_ready = false;
 * ```
 */
#define OTTF_BACKDOOR_VAR OT_USED OT_SECTION(".data") volatile

/**
 * Same as `OTTF_BACKDOOR_VAR` but for DV environments.
 * ```
 */
#define OTTF_BACKDOOR_VAR_DV OT_USED OT_SECTION(".rodata") volatile

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_UTILS_H_
