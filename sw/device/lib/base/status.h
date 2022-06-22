// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_STATUS_H_
#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"

#define USING_ABSL_STATUS
#include "sw/device/lib/base/absl_status.h"
#undef USING_ABSL_STATUS

#ifdef __cplusplus
extern "C" {
#endif

/**
 * We use the error category codes from absl_status.h.  We build a packed
 * status value that identifies the source of the error (in the form of the
 * module identifier and line number).
 *
 * By default, the module identifier is the first three letters of the
 * source filename.  The identifier can be overridden (per-module) with the
 * DECLARE_MODULE_ID macro.
 *
 * Our status codes are arranged as a packed bitfield, with the sign
 * bit signifying whether the value represents a result or an error.
 *
 * All Ok (good) values:
 * 32  31                                             0
 *  +---+---------------------------------------------+
 *  |   |                  31 bit                     |
 *  | 0 |                  Result                     |
 *  +---+---------------------------------------------+
 *
 * All Error values:
 * 32  31      26      21      16             5       0
 *  +---+-------+-------+-------+-------------+-------+
 *  |   |   15 bit              | 11 bit      | 5 bit |
 *  | 1 |   Module Identifier   | Line Number | code  |
 *  +---+-------+-------+-------+-------------+-------+
 *
 * The module identifier value is interpreted as three 5-bit fields
 * representing the characters [0x40..0x5F] (e.g. [@ABC ... _]).
 */

#define STATUS_FIELD_CODE ((bitfield_field32_t){.mask = 0x1f, .index = 0})
#define STATUS_FIELD_ARG ((bitfield_field32_t){.mask = 0x7ff, .index = 5})
#define STATUS_FIELD_MODULE_ID \
  ((bitfield_field32_t){.mask = 0x7fff, .index = 16})
#define STATUS_BIT_ERROR 31
typedef struct status {
  int32_t value;
} status_t;

// Uses a GCC statement-expr to embed conrtol-flow inside an expression.
#define TRY(expr_)            \
  ({                          \
    status_t status_ = expr_; \
    if (status_.value < 0) {  \
      return status_;         \
    }                         \
    status_.value;            \
  })

// This global constant is available to all modules and is the constant zero.
extern const uint32_t status_module_id;
// clang-format off
#define ASCII_5BIT(v) ( \
    /*uppercase characters*/  (v) >= '@' && (v) <= '_' ? (v) - '@' \
    /*lower cvt upper*/     : (v) >= '`' && (v) <= 'z' ? (v) - '`' \
    /*else cvt underscore*/ : '_' - '@'                            \
  )
// clang-format on

#define MAKE_MODULE_ID(a, b, c) \
  (ASCII_5BIT(a) << 16) | (ASCII_5BIT(b) << 21) | (ASCII_5BIT(c) << 26)
// A module that uses DECLARE_MODULE_ID shadows the global constant value with
// its own local value.
#define DECLARE_MODULE_ID(a, b, c) \
  static uint32_t status_module_id = MAKE_MODULE_ID(a, b, c)

// Operations on status codes:
/**
 * Creates a packed status_t.
 *
 * @param code An absl_status code.
 * @param mod_id The module creating the status code.
 * @param file The filename of the module creating the code.
 * @param arg The argument associated with the status.
 * @return `status_t`.
 */
status_t status_create(absl_status_t code, uint32_t mod_id, const char *file,
                       int32_t arg);

/**
 * Extracts the packed values from a status code.
 *
 * @param s The status code to extract values from.
 * @param code Pointer to the english name of the status code.
 * @param arg Pointer to an integer argument.
 * @param mod_id Pointer to a char[3] buffer for the module id.
 * @return True if the status represents and error, False if the status
 * represents Ok.
 */
bool status_extract(status_t s, const char **code, int32_t *arg, char *mod_id);

/**
 * Returns whether the status value represents Ok.
 *
 * @param s The status code.
 * @return True if the status represents Ok.
 */
OT_ALWAYS_INLINE bool status_ok(status_t s) { return s.value >= 0; }

/**
 * Returns the absl status code in the status.
 *
 * @param s The status code.
 * @return `absl_status_t` contained within the status_t.
 */
OT_ALWAYS_INLINE absl_status_t status_err(status_t s) {
  return s.value < 0
             ? (absl_status_t)bitfield_field32_read(s.value, STATUS_FIELD_CODE)
             : kOk;
}

// Create a status with an optional argument.
// TODO(cfrantz, alphan): Figure out how we want to create statuses in
// silicon_creator code.
#define STATUS_CREATE(s_, ...)                            \
  ({                                                      \
    static_assert(OT_VA_ARGS_COUNT(_, __VA_ARGS__) <= 2,  \
                  "status macros take 0 or 1 arguments"); \
    status_create(s_, status_module_id, __FILE__,         \
                  OT_GET_LAST_ARG(__VA_ARGS__));          \
  })

// Helpers for creating statuses of various kinds.
// clang-format off
#define OK_STATUS(...)           STATUS_CREATE(kOk,                 0,        ##__VA_ARGS__)
#define CANCELLED(...)           STATUS_CREATE(kCancelled,          __LINE__, ##__VA_ARGS__)
#define UNKNOWN(...)             STATUS_CREATE(kUnknown,            __LINE__, ##__VA_ARGS__)
#define INVALID_ARGUMENT(...)    STATUS_CREATE(kInvalidArgument,    __LINE__, ##__VA_ARGS__)
#define DEADLINE_EXCEEDED(...)   STATUS_CREATE(kDeadlineExceeded,   __LINE__, ##__VA_ARGS__)
#define NOT_FOUND(...)           STATUS_CREATE(kNotFound,           __LINE__, ##__VA_ARGS__)
#define ALREADY_EXISTS(...)      STATUS_CREATE(kAlreadyExists,      __LINE__, ##__VA_ARGS__)
#define PERMISSION_DENIED(...)   STATUS_CREATE(kPermissionDenied,   __LINE__, ##__VA_ARGS__)
#define RESOURCE_EXHAUSTED(...)  STATUS_CREATE(kResourceExhausted,  __LINE__, ##__VA_ARGS__)
#define FAILED_PRECONDITION(...) STATUS_CREATE(kFailedPrecondition, __LINE__, ##__VA_ARGS__)
#define ABORTED(...)             STATUS_CREATE(kAborted,            __LINE__, ##__VA_ARGS__)
#define OUT_OF_RANGE(...)        STATUS_CREATE(kOutOfRange,         __LINE__, ##__VA_ARGS__)
#define UNIMPLEMENTED(...)       STATUS_CREATE(kUnimplemented,      __LINE__, ##__VA_ARGS__)
#define INTERNAL(...)            STATUS_CREATE(kInternal,           __LINE__, ##__VA_ARGS__)
#define UNAVAILABLE(...)         STATUS_CREATE(kUnavailable,        __LINE__, ##__VA_ARGS__)
#define DATA_LOSS(...)           STATUS_CREATE(kDataLoss,           __LINE__, ##__VA_ARGS__)
#define UNAUTHENTICATED(...)     STATUS_CREATE(kUnauthenticated,    __LINE__, ##__VA_ARGS__)
// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_STATUS_H_
