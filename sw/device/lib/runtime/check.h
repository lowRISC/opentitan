// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0`

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_CHECK_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_CHECK_H_

#include <stdbool.h>

#include "sw/device/lib/base/log.h"
#include "sw/device/lib/runtime/abort.h"

/**
 * Runtime assertion macros with log.h integration.
 */

/**
 * Checks that the given condition is true. If the condition is false, this
 * function logs and then aborts.
 *
 * @param condition an expression to check.
 * @param ... arguments to a LOG_* macro, which are evaluated if the check
 * fails.
 */
#define CHECK(condition, ...)                \
  do {                                       \
    if (!(condition)) {                      \
      LOG_ERROR("CHECK-fail: " __VA_ARGS__); \
      abort();                               \
    }                                        \
  } while (false)

/**
 * Shorthand for CHECK(value == 0).
 *
 * @param condition a value to check.
 * @param ... arguments to a LOG_* macro, which are evaluated if the check
 * fails.
 */
#define CHECKZ(value, ...) CHECK((value) == 0, ...)

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_CHECK_H_
