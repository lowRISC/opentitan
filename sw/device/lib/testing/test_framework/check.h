// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_CHECK_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_CHECK_H_

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/status.h"

/**
 * Runtime assertion macros with log.h integration.
 */

#ifdef __cplusplus
#error "This file is C-only; it is not a polyglot header!"
#endif

/**
 * Checks that the given condition is true. If the condition is false, this
 * function logs and then aborts.
 *
 * @param condition An expression to check.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check
 * fails.
 */
#define CHECK(condition, ...)                        \
  do {                                               \
    if (!(condition)) {                              \
      /* NOTE: because the condition in this if      \
         statement can be statically determined,     \
         only one of the below string constants      \
         will be included in the final binary.*/     \
      if (OT_VA_ARGS_COUNT(_, ##__VA_ARGS__) == 0) { \
        LOG_ERROR("CHECK-fail: " #condition);        \
      } else {                                       \
        LOG_ERROR("CHECK-fail: " __VA_ARGS__);       \
      }                                              \
      /* Currently, this macro will call into        \
         the test failure code, which logs           \
         "FAIL" and aborts. In the future,           \
         we will try to condition on whether         \
         or not this is a test.*/                    \
      test_status_set(kTestStatusFailed);            \
    }                                                \
  } while (false)

// Note that this is *not* a polyglot header, so we can use the C11-only
// _Generic keyword safely.
// See: https://en.cppreference.com/w/c/language/generic
// clang-format off
#define SHOW_MISMATCH_FMT_STR_(a) _Generic((a),                 \
          bool: "CHECK-fail: [%d] got: 0x%02x; want: 0x%02x",   \
        int8_t: "CHECK-fail: [%d] got: 0x%02x; want: 0x%02x",   \
       uint8_t: "CHECK-fail: [%d] got: 0x%02x; want: 0x%02x",   \
       int16_t: "CHECK-fail: [%d] got: 0x%04x; want: 0x%04x",   \
      uint16_t: "CHECK-fail: [%d] got: 0x%04x; want: 0x%04x",   \
       int32_t: "CHECK-fail: [%d] got: 0x%08x; want: 0x%08x",   \
      uint32_t: "CHECK-fail: [%d] got: 0x%08x; want: 0x%08x",   \
       int64_t: "CHECK-fail: [%d] got: 0x%016x; want: 0x%016x", \
      uint64_t: "CHECK-fail: [%d] got: 0x%016x; want: 0x%016x")
#define SHOW_MATCH_FMT_STR_(a) _Generic((a),            \
          bool: "CHECK-fail: [%d] both equal: 0x%02x",  \
        int8_t: "CHECK-fail: [%d] both equal: 0x%02x",  \
       uint8_t: "CHECK-fail: [%d] both equal: 0x%02x",  \
       int16_t: "CHECK-fail: [%d] both equal: 0x%04x",  \
      uint16_t: "CHECK-fail: [%d] both equal: 0x%04x",  \
       int32_t: "CHECK-fail: [%d] both equal: 0x%08x",  \
      uint32_t: "CHECK-fail: [%d] both equal: 0x%08x",  \
       int64_t: "CHECK-fail: [%d] both equal: 0x%016x", \
      uint64_t: "CHECK-fail: [%d] both equal: 0x%016x")
// clang-format on

/**
 * Compare `num_items_` of `actual_` against `expected_` buffer.
 *
 * Prints differences between `actual_` and `expected_` before logging an error.
 * Note, the differences between the actual and expected buffer values are
 * logged via LOG_INFO _before_ the error is logged with LOG_ERROR, since by
 * default DV simulations are configured to terminate upon the first error.
 *
 * @param actual_ Buffer containing actual values.
 * @param expected_ Buffer containing expected values.
 * @param num_items_ Number of items to compare.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check.
 */
#define CHECK_ARRAYS_EQ(actual_, expected_, num_items_, ...)                  \
  do {                                                                        \
    static_assert(sizeof(*(actual_)) == sizeof(*(expected_)),                 \
                  "CHECK_ARRAYS requires arguments of equal size.");          \
    bool fail = false;                                                        \
    for (size_t i = 0; i < num_items_; ++i) {                                 \
      if ((actual_)[i] != (expected_)[i]) {                                   \
        if (!fail) {                                                          \
          /* Print a failure message as soon as possible. */                  \
          if (OT_VA_ARGS_COUNT(_, ##__VA_ARGS__) == 0) {                      \
            LOG_ERROR("CHECK-fail: " #actual_ " does not match " #expected_); \
          } else {                                                            \
            LOG_ERROR("CHECK-fail: " __VA_ARGS__);                            \
          }                                                                   \
        }                                                                     \
                                                                              \
        LOG_ERROR(SHOW_MISMATCH_FMT_STR_((actual_)[i]), i, (actual_)[i],      \
                  (expected_)[i]);                                            \
        fail = true;                                                          \
      }                                                                       \
    }                                                                         \
    if (fail) {                                                               \
      /* Currently, this macro will call into                                 \
          the test failure code, which logs                                   \
          "FAIL" and aborts. In the future,                                   \
          we will try to condition on whether                                 \
          or not this is a test.*/                                            \
      test_status_set(kTestStatusFailed);                                     \
    }                                                                         \
  } while (false)

/**
 * Compare `num_items_` of `actual_` against `not_expected_` buffer.
 *
 * Prints matches between `actual_` and `not_expected_` before logging an error.
 * Note, the matches between the actual and not_expected buffer values are
 * logged via LOG_INFO _before_ the error is logged with LOG_ERROR, since by
 * default DV simulations are configured to terminate upon the first error.
 *
 * @param actual_ Buffer containing actual values.
 * @param not_expected_ Buffer containing not expected values.
 * @param num_items_ Number of items to compare.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check.
 */
#define CHECK_ARRAYS_NE(actual_, not_expected_, num_items_, ...)               \
  do {                                                                         \
    static_assert(sizeof(*(actual_)) == sizeof(*(not_expected_)),              \
                  "CHECK_ARRAYS requires arguments of equal size.");           \
    if (memcmp((actual_), (not_expected_), num_items_ * sizeof(*(actual_))) == \
        0) {                                                                   \
      if (OT_VA_ARGS_COUNT(_, ##__VA_ARGS__) == 0) {                           \
        LOG_ERROR("CHECK-fail: " #actual_ " matches " #not_expected_);         \
      } else {                                                                 \
        LOG_ERROR("CHECK-fail: " __VA_ARGS__);                                 \
      }                                                                        \
      for (size_t i = 0; i < num_items_; ++i) {                                \
        LOG_ERROR(SHOW_MATCH_FMT_STR_((actual_)[i]), i, (actual_)[i]);         \
      }                                                                        \
      /* Currently, this macro will call into                                  \
          the test failure code, which logs                                    \
          "FAIL" and aborts. In the future,                                    \
          we will try to condition on whether                                  \
          or not this is a test.*/                                             \
      test_status_set(kTestStatusFailed);                                      \
    }                                                                          \
  } while (false)

/**
 * Checks the characters of two strings are the same,
 * up to and including the first null character.
 * The CHECK macro is called on each character pair.
 *
 * @param actual_ The first string in the comparison.
 * @param expected_ The second string in the comparison.
 */
#define CHECK_STR_EQ(actual_, expected_)                                  \
  do {                                                                    \
    size_t i = 0;                                                         \
    const char *expected = (expected_);                                   \
    const char *actual = (actual_);                                       \
    do {                                                                  \
      CHECK(actual[i] == expected[i],                                     \
            "Strings differ at char %d, so \"%s\" != \"%s\".", i, actual, \
            expected);                                                    \
      ++i;                                                                \
    } while (actual[i] != '\0' || expected[i] != '\0');                   \
  } while (false)

/**
 * Checks that the given DIF call returns kDifOk. If the DIF call returns a
 * different dif_result_t value (defined in sw/device/lib/dif/dif_base.h), this
 * function logs and then aborts.
 *
 * @param dif_call DIF call to invoke and check its return value.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check
 * fails.
 */
#define CHECK_DIF_OK(dif_call, ...)                                  \
  do {                                                               \
    dif_result_t dif_result = dif_call;                              \
    if (dif_result != kDifOk) {                                      \
      /* NOTE: because the condition in this if                      \
         statement can be statically determined,                     \
         only one of the below string constants                      \
         will be included in the final binary.*/                     \
      if (OT_VA_ARGS_COUNT(_, ##__VA_ARGS__) == 0) {                 \
        LOG_ERROR("DIF-fail: " #dif_call " returns %d", dif_result); \
      } else {                                                       \
        LOG_ERROR("DIF-fail: " __VA_ARGS__);                         \
      }                                                              \
      /* Currently, this macro will call into                        \
         the test failure code, which logs                           \
         "FAIL" and aborts. In the future,                           \
         we will try to condition on whether                         \
         or not this is a test.*/                                    \
      test_status_set(kTestStatusFailed);                            \
    }                                                                \
  } while (false)

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_CHECK_H_
