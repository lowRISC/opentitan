// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Values in `status_t` that are guaranteed to correspond to each
 * `otcrypto_status_t` value.
 *
 * If `OTCRYPTO_STATUS_DEBUG` is set, full line-number and module information
 * is included to ease debugging. Otherwise, we use the cryptolib error codes
 * directly.
 *
 * Note: These values bypass `status_create` to avoid having a function call in
 * error cases, where we may be under attack and complexity should be
 * minimized.
 */
#define OTCRYPTO_OK ((status_t){.value = kHardenedBoolTrue})
#ifdef OTCRYPTO_STATUS_DEBUG

#define OTCRYPTO_RECOV_ERR                                \
  ((status_t){.value = (int32_t)(0x80000000 | MODULE_ID | \
                                 ((__LINE__ & 0x7ff) << 5) | kAborted)})
#define OTCRYPTO_FATAL_ERR                           \
  ((status_t){.value =                               \
                  (int32_t)(0x80000000 | MODULE_ID | \
                            ((__LINE__ & 0x7ff) << 5) | kFailedPrecondition)})
#define OTCRYPTO_BAD_ARGS                            \
  ((status_t){.value =                               \
                  (int32_t)(0x80000000 | MODULE_ID | \
                            ((__LINE__ & 0x7ff) << 5) | kInvalidArgument)})
#define OTCRYPTO_ASYNC_INCOMPLETE                         \
  ((status_t){.value = (int32_t)(0x80000000 | MODULE_ID | \
                                 ((__LINE__ & 0x7ff) << 5) | kUnavailable)})
#define OTCRYPTO_NOT_IMPLEMENTED                          \
  ((status_t){.value = (int32_t)(0x80000000 | MODULE_ID | \
                                 ((__LINE__ & 0x7ff) << 5) | kUnimplemented)})
#else

#define OTCRYPTO_RECOV_ERR \
  ((status_t){.value = kOtcryptoStatusValueInternalError})
#define OTCRYPTO_FATAL_ERR ((status_t){.value = kOtcryptoStatusValueFatalError})
#define OTCRYPTO_BAD_ARGS ((status_t){.value = kOtcryptoStatusValueBadArgs})
#define OTCRYPTO_ASYNC_INCOMPLETE \
  ((status_t){.value = kOtcryptoStatusValueAsyncIncomplete})
#define OTCRYPTO_NOT_IMPLEMENTED \
  ((status_t){.value = kOtcryptoStatusValueNotImplemented})

#endif

#ifndef OT_DISABLE_HARDENING
/**
 * Hardened version of the `TRY` macro from `status.h`.
 *
 * Returns an error if either expr_ represents an error, or if the OK code does
 * not match the expected hardened value.
 *
 * @param expr_ An expression that evaluates to a `status_t`.
 * @return The enclosed OK value.
 */
#define HARDENED_TRY(expr_)                                             \
  do {                                                                  \
    status_t status_ = expr_;                                           \
    if (launder32(OT_UNSIGNED(status_.value)) != kHardenedBoolTrue) {   \
      return (status_t){                                                \
          .value = (int32_t)(OT_UNSIGNED(status_.value) | 0x80000000)}; \
    }                                                                   \
    HARDENED_CHECK_EQ(status_.value, kHardenedBoolTrue);                \
    status_.value;                                                      \
  } while (false)

#else  // OT_DISABLE_HARDENING

/**
 * Alternate version of HARDENED_TRY that is logically equivalent.
 *
 * This can be used to measure the code size and performance impact of
 * control-flow countermeasures.
 *
 * @param expr_ An expression that evaluates to a `status_t`.
 * @return The enclosed OK value.
 */
#define HARDENED_TRY(expr_)                                             \
  do {                                                                  \
    status_t status_ = expr_;                                           \
    if (status_.value != kHardenedBoolTrue) {                           \
      return (status_t){                                                \
          .value = (int32_t)(OT_UNSIGNED(status_.value) | 0x80000000)}; \
    }                                                                   \
    status_.value;                                                      \
  } while (false)

#endif  // OT_DISABLE_HARDENING

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
