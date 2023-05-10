// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_CHECK_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_CHECK_H_

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
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
 * function logs and then returns a `kInternal` error.
 *
 * @param condition An expression to check.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check
 * fails.
 */
#define CHECK_IMPL(condition, ...)                                         \
  ({                                                                       \
    status_t sts_ = OK_STATUS();                                           \
    /* NOTE: The volatile intermediate variable is added to guarantee that \
     * this macro won't be optimized out when used with compiling time     \
     * constants.*/                                                        \
    volatile bool res_ = (condition);                                      \
    if (!res_) {                                                           \
      /* NOTE: because the condition in this if                            \
         statement can be statically determined,                           \
         only one of the below string constants                            \
         will be included in the final binary.*/                           \
      if (OT_VA_ARGS_COUNT(_, ##__VA_ARGS__) == 0) {                       \
        LOG_ERROR("CHECK-fail: " #condition);                              \
      } else {                                                             \
        LOG_ERROR("CHECK-fail: " __VA_ARGS__);                             \
      }                                                                    \
      sts_ = INTERNAL();                                                   \
    }                                                                      \
    sts_;                                                                  \
  })

/**
 * Checks that the given condition is true. If the condition is false, this
 * function logs and then aborts.
 *
 * @param condition An expression to check.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check
 * fails.
 */
#define CHECK(condition, ...)                               \
  do {                                                      \
    if (status_err(CHECK_IMPL(condition, ##__VA_ARGS__))) { \
      /* Currently, this macro will call into               \
         the test failure code, which logs                  \
         "FAIL" and aborts. In the future,                  \
         we will try to condition on whether                \
         or not this is a test.*/                           \
      test_status_set(kTestStatusFailed);                   \
    }                                                       \
  } while (false)

/**
 * Same as `CHECK` above but returns a status_t if false rather than aborting.
 */
#define TRY_CHECK(condition, ...) TRY(CHECK_IMPL(condition, ##__VA_ARGS__))

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
 * Compare `actual_` against `ref_` buffer.
 *
 * Prints matches between `actual_` and `ref_` before logging an error.
 *
 * @param expect_eq_ True if the arrays are expected to be equal, false
 * otherwise.
 * @param actual_ Buffer containing actual values.
 * @param ref_ Buffer containing the reference values.
 * @param size_ Number of items to compare.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check.
 * @return Either `kOk` or `kInternal`.
 */

#define CHECK_ARRAYS_IMPL(expect_eq_, actual_, ref_, size_, ...)           \
  ({                                                                       \
    static_assert(sizeof(*(actual_)) == sizeof(*(ref_)),                   \
                  "CHECK_ARRAYS requires arguments of equal size.");       \
    status_t sts_ = OK_STATUS();                                           \
    volatile bool is_eq =                                                  \
        memcmp((actual_), (ref_), size_ * sizeof(*(actual_))) == 0;        \
    if (is_eq != expect_eq_) {                                             \
      if (OT_VA_ARGS_COUNT(_, ##__VA_ARGS__) == 0) {                       \
        LOG_ERROR("CHECK-fail: " #actual_ "%smatches " #ref_,              \
                  expect_eq_ ? " un" : " ");                               \
      } else {                                                             \
        LOG_ERROR("CHECK-fail: " __VA_ARGS__);                             \
      }                                                                    \
      for (size_t i = 0; i < size_; ++i) {                                 \
        if (expect_eq_) {                                                  \
          LOG_ERROR(SHOW_MISMATCH_FMT_STR_((actual_)[i]), i, (actual_)[i], \
                    (ref_)[i]);                                            \
        } else {                                                           \
          LOG_ERROR(SHOW_MATCH_FMT_STR_((actual_)[i]), i, (actual_)[i]);   \
        }                                                                  \
      }                                                                    \
      sts_ = INTERNAL();                                                   \
    }                                                                      \
    sts_;                                                                  \
  })

/**
 * Compare `num_items_` of `actual_` against `expected_` buffer.
 *
 * Prints differences between `actual_` and `expected_` before logging an error.
 * Note in case the arrays are not equal the test will be terminated.
 * @param actual_ Buffer containing actual values.
 * @param expected_ Buffer containing expected values.
 * @param num_items_ Number of items to compare.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check.
 */
#define CHECK_ARRAYS_EQ(actual_, expected_, num_items_, ...)               \
  do {                                                                     \
    if (status_err(CHECK_ARRAYS_IMPL(true, actual_, expected_, num_items_, \
                                     ##__VA_ARGS__))) {                    \
      /* Currently, this macro will call into the test failure code,       \
      which logs "FAIL" and aborts. In the future, we will try to          \
      condition on whether or not this is a test.*/                        \
      test_status_set(kTestStatusFailed);                                  \
    }                                                                      \
  } while (false)

/**
 * Same as `CHECK_ARRAYS_EQ` above but returns `kInternal` if the arrays are not
 * equal rather than aborting.
 */
#define TRY_CHECK_ARRAYS_EQ(actual_, expected_, num_items_, ...) \
  TRY(CHECK_ARRAYS_IMPL(true, actual_, expected_, num_items_, ##__VA_ARGS__))

/**
 * Same as `CHECK_ARRAYS_NE` above but returns `kInternal` if the arrays are not
 * equal rather than aborting.
 */
#define TRY_CHECK_ARRAYS_NE(actual_, expected_, num_items_, ...) \
  TRY(CHECK_ARRAYS_IMPL(false, actual_, expected_, num_items_, ##__VA_ARGS__))

/**
 * Compare `num_items_` of `actual_` against `not_expected_` buffer.
 *
 * Prints matches between `actual_` and `not_expected_` before logging an error.
 *
 * @param actual_ Buffer containing actual values.
 * @param not_expected_ Buffer containing not expected values.
 * @param num_items_ Number of items to compare.
 * @param ... Arguments to a LOG_* macro, which are evaluated if the check.
 */
#define CHECK_ARRAYS_NE(actual_, not_expected_, num_items_, ...)            \
  do {                                                                      \
    if (status_err(CHECK_ARRAYS_IMPL(false, actual_, not_expected_,         \
                                     num_items_, ##__VA_ARGS__))) {         \
      /* Currently, this macro will call into the test failure code, which  \
         logs "FAIL" and aborts. In the future, we will try to condition on \
         whether or not this is a test.*/                                   \
      test_status_set(kTestStatusFailed);                                   \
    }                                                                       \
  } while (false)

/**
 * Checks the characters of two strings are the same, up to and including the
 * first null character. The CHECK macro is called on each character pair.
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

/**
 * Prints `status_t` using a format compatible with DV.
 *
 * The %r specifier supported by the software print module is no compatible with
 * the DV environment.
 *
 * If you landed here after reviewing a DV error log: Please read the status.h
 * documentation for more details on how `status_t` encodes the module id, line
 * number and error code.
 *
 * @param expr An expression which evaluates to a `status_t`.
 *
 */
#define _LOG_ERROR_STATUS_DV(expr)                                         \
  do {                                                                     \
    status_t status_ = expr;                                               \
    const char *msg;                                                       \
    char mod_id[3] = {0};                                                  \
    int line;                                                              \
    if (status_extract(status_, &msg, &line, mod_id)) {                    \
      LOG_ERROR("CHECK-STATUS-fail: %c%c%c:%d = %s", mod_id[0], mod_id[1], \
                mod_id[2], line, msg);                                     \
    } else {                                                               \
      LOG_ERROR("CHECK-STATUS-fail: 0x%08x", status_);                     \
    }                                                                      \
  } while (false)

/**
 * Unwrap a `status_t` when it represents a non-error value, otherwise prints a
 * human-readable error message and abort.
 *
 * @param expr An expression which evaluates to a `status_t`.
 */
#define UNWRAP(expr, ...)                            \
  ({                                                 \
    status_t status_ = expr;                         \
    if (!status_ok(status_)) {                       \
      if (kDeviceLogBypassUartAddress) {             \
        _LOG_ERROR_STATUS_DV(status_);               \
      } else {                                       \
        LOG_ERROR("CHECK-STATUS-fail: %r", status_); \
      }                                              \
      test_status_set(kTestStatusFailed);            \
    }                                                \
    status_.value;                                   \
  })

/**
 * Checks that the `status_t` represents a non-error value.
 *
 * Prints a human-readable error message if the status represents an error.
 *
 * @param expr An expression which evaluates to a `status_t`.
 */
#define CHECK_STATUS_OK(expr, ...)                   \
  do {                                               \
    status_t status_ = expr;                         \
    if (!status_ok(status_)) {                       \
      if (kDeviceLogBypassUartAddress) {             \
        _LOG_ERROR_STATUS_DV(status_);               \
      } else {                                       \
        LOG_ERROR("CHECK-STATUS-fail: %r", status_); \
      }                                              \
      test_status_set(kTestStatusFailed);            \
    }                                                \
  } while (false)

/**
 * Checks that the `status_t` represents a error value.
 *
 * Prints a human-readable error message if the status represents an non-error.
 *
 * @param expr An expression which evaluates to a `status_t`.
 */
#define CHECK_STATUS_NOT_OK(expr, ...)               \
  do {                                               \
    status_t status_ = expr;                         \
    if (status_ok(status_)) {                        \
      if (kDeviceLogBypassUartAddress) {             \
        _LOG_ERROR_STATUS_DV(status_);               \
      } else {                                       \
        LOG_ERROR("CHECK-STATUS-fail: %r", status_); \
      }                                              \
      test_status_set(kTestStatusFailed);            \
    }                                                \
  } while (false)

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_CHECK_H_
