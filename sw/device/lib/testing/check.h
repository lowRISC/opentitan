// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_CHECK_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_CHECK_H_

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_status.h"

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
#define CHECK(condition, ...)                             \
  do {                                                    \
    if (!(condition)) {                                   \
      /* NOTE: because the condition in this if           \
         statement can be statically determined,          \
         only one of the below string constants           \
         will be included in the final binary.*/          \
      if (GET_NUM_VARIABLE_ARGS(_, ##__VA_ARGS__) == 0) { \
        LOG_ERROR("CHECK-fail: " #condition);             \
      } else {                                            \
        LOG_ERROR("CHECK-fail: " __VA_ARGS__);            \
      }                                                   \
      /* Currently, this macro will call into             \
         the test failure code, which logs                \
         "FAIL" and aborts. In the future,                \
         we will try to condition on whether              \
         or not this is a test.*/                         \
      test_status_set(kTestStatusFailed);                 \
    }                                                     \
  } while (false)

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_CHECK_H_
