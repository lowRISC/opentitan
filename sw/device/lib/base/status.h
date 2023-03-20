// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_STATUS_H_
#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/silicon_creator/lib/error.h"

#define USING_INTERNAL_STATUS
#include "sw/device/lib/base/internal/status.h"
#undef USING_INTERNAL_STATUS

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
typedef struct status {
  int32_t value;
} status_t;

#define DIF_RESULT_INTO_STATUS(expr_)                                     \
  ({                                                                      \
    typeof(expr_) _val = (expr_);                                         \
    absl_status_t code;                                                   \
    memcpy(&code, &_val, sizeof(code));                                   \
    status_create(code, MODULE_ID, __FILE__, code == kOk ? 0 : __LINE__); \
  })

#define ROM_ERROR_INTO_STATUS(expr_)                                          \
  ({                                                                          \
    typeof(expr_) ex_ = (expr_);                                              \
    uint32_t val;                                                             \
    memcpy(&val, &ex_, sizeof(val));                                          \
    absl_status_t code =                                                      \
        val == kErrorOk ? 0                                                   \
                        : bitfield_field32_read(val, ROM_ERROR_FIELD_STATUS); \
    int32_t arg = bitfield_field32_read(val, ROM_ERROR_FIELD_ERROR);          \
    uint32_t mod = bitfield_field32_read(val, ROM_ERROR_FIELD_MODULE);        \
    uint32_t module = (mod & 0x1F) << 16 | (mod & 0x1F00) << (21 - 8);        \
    status_create(code, module, __FILE__, code == kOk ? kErrorOk : arg);      \
  })

/**
 * Converts a value into a status_t.
 *
 * This macro uses the C11 `_Generic` feature to detect the type of the input
 * expression and apply the appropriate conversion.  Once a more thorough
 * refactoring of the DIFs is done, this can be eliminated.
 *
 * @param expr_ Either a `status_t`, `dif_result_t` or `rom_error_t`.
 * @return The `status_t` representation of the input.
 */
// clang-format off
  #define INTO_STATUS(expr_) _Generic((expr_),                                   \
           status_t: (expr_),                                                   \
        rom_error_t: ROM_ERROR_INTO_STATUS(expr_),                              \
       dif_result_t: DIF_RESULT_INTO_STATUS(expr_))
// clang-format on

/**
 * Evaluates a status_t for Ok or Error status, returning the Ok value.
 *
 * This macro is like the `try!` macro (or now `?` operator) in Rust:
 * It evaluates to the contained OK value or it immediately returns from
 * the enclosing function with the error value.
 *
 * @param expr_ An expression that can be converted to a `status_t`.
 * @return The enclosed OK value.
 */
#define TRY(expr_)                         \
  ({                                       \
    status_t status_ = INTO_STATUS(expr_); \
    if (status_.value < 0) {               \
      return status_;                      \
    }                                      \
    status_.value;                         \
  })

// This global constant is available to all modules and is the constant zero.
// This name intentionally violates the constant naming convention of
// `kModuleId` because users are expected to provide an override in the form
// of a preprocessor defintion: `#define MODULE_ID MAKE_MODULE_ID(...)`.
extern const uint32_t MODULE_ID;

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
#define STATUS_CREATE(s_, ...)                                            \
  ({                                                                      \
    static_assert(OT_VA_ARGS_COUNT(_, __VA_ARGS__) <= 2,                  \
                  "status macros take 0 or 1 arguments");                 \
    status_create(s_, MODULE_ID, __FILE__, OT_GET_LAST_ARG(__VA_ARGS__)); \
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
