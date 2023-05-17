// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_STATUS_H_

/**
 * @file
 * @brief Hardened handling of status codes.
 */

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Hardened variant of `OK_STATUS` .
 *
 * This passes `kHardenedBoolTrue` as the status code argument, for extra bits
 * of redundancy in `HARDENED_TRY` and others.
 */
#define HARDENED_OK_STATUS ((status_t){.value = kHardenedBoolTrue})

/**
 * Hardened version of the `TRY` macro from `status.h`.
 *
 * Returns the error unmodified if `status_ok` fails, and throws an
 * `INTERNAL()` error if the OK code does not match the hardened value.
 *
 * @param expr_ An expression that evaluates to a `status_t`.
 * @return The enclosed OK value.
 */
#define HARDENED_TRY(expr_)                              \
  ({                                                     \
    status_t status_ = expr_;                            \
    if (!status_ok(status_)) {                           \
      return status_;                                    \
    }                                                    \
    if (launder32(status_.value) != kHardenedBoolTrue) { \
      return INTERNAL();                                 \
    }                                                    \
    HARDENED_CHECK_EQ(status_.value, kHardenedBoolTrue); \
    status_.value;                                       \
  })

/**
 * Hardened version of `status_ok`.
 *
 * Returns `kHardenedBoolTrue` if the status is OK with an argument code of
 * `kHardenedBoolTrue` (i.e. equal to `HARDENED_OK_STATUS`), and
 * `kHardenedBoolFalse` otherwise.
 *
 * @param s The status code.
 * @return True if the status represents Ok.
 */
hardened_bool_t hardened_status_ok(status_t s);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_STATUS_H_
