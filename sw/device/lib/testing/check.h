// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_CHECK_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_CHECK_H_

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

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

/**
 * Compare `num_items_` of `actual_` against `expected_` buffer.
 *
 * Prints differences between `actual_` and `expected_` before assiging the
 * comparison `result_` value.
 *
 * @param[out] result_ Result of the comparison.
 * @param actual_ Buffer containing actual values.
 * @param expected_ Buffer containing expected values.
 * @param num_items_ Number of items to compare.
 */
#define CHECK_BUFFER(result_, actual_, expected_, num_items_)                 \
  do {                                                                        \
    /* `sizeof(actual_[0])` is used to determine the size of each item in the \
     * buffer. */                                                             \
    if (memcmp(actual_, expected_, num_items_ * sizeof(actual_[0])) != 0) {   \
      for (size_t i = 0; i < num_items_; ++i) {                               \
        LOG_ERROR("[%d] actual = 0x%x; expected = 0x%x", i, actual_[i],       \
                  expected_[i]);                                              \
      }                                                                       \
      result_ = false;                                                        \
    } else {                                                                  \
      result_ = true;                                                         \
    }                                                                         \
  } while (false)

/**
 * Checks that the given DIF call returns kDifOk. If the DIF call returns a
 * different dif_result_t value (defined in sw/device/lib/dif/dif_base.h), this
 * function logs and then aborts.
 *
 * @param DIF call to invoke and check its return value .
 * @param ... arguments to a LOG_* macro, which are evaluated if the check
 * fails.
 */
#define CHECK_DIF_OK(dif_call, ...)                       \
  do {                                                    \
    if (dif_call != kDifOk) {                             \
      /* NOTE: because the condition in this if           \
         statement can be statically determined,          \
         only one of the below string constants           \
         will be included in the final binary.*/          \
      if (GET_NUM_VARIABLE_ARGS(_, ##__VA_ARGS__) == 0) { \
        LOG_ERROR("CHECK-fail: " #dif_call);              \
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
