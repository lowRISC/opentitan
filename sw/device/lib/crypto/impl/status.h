// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_

#include "sw/device/lib/base/hardened_status.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Values in `status_t` that are guaranteed to correspond to each
 * `crypto_status_t` value.
 *
 * If `OTCRYPTO_STATUS_DEBUG` is set, full line-number and module information
 * is included to ease debugging. Otherwise, we use the cryptolib error codes
 * directly.
 *
 * Note: These values bypass `status_create` to avoid having a function call in
 * error cases, where we may be under attack and complexity should be
 * minimized.
 */
#define OTCRYPTO_OK HARDENED_OK_STATUS
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
  ((status_t){.value = (int32_t)kCryptoStatusInternalError})
#define OTCRYPTO_FATAL_ERR \
  ((status_t){.value = (int32_t)kCryptoStatusFatalError})
#define OTCRYPTO_BAD_ARGS ((status_t){.value = (int32_t)kCryptoStatusBadArgs})
#define OTCRYPTO_ASYNC_INCOMPLETE \
  ((status_t){.value = (int32_t)kCryptoStatusAsyncIncomplete})
#define OTCRYPTO_NOT_IMPLEMENTED \
  ((status_t){.value = (int32_t)kCryptoStatusNotImplemented})

#endif

/**
 * Convert a `status_t` into a `crypto_status_t`.
 *
 * Use the OTCRYPTO_* macros and turn off OTCRYPTO_STATUS_DEBUG to ensure valid
 * `crypto_status_t` results. Otherwise, it is possible to get values that are
 * not members of the enum; since cryptolib status codes are bit-compatible
 * with `status_t`, we just cast and return them.
 *
 * @param status Initial `status_t` value.
 * @return Equivalent `crypto_status_t` error code.
 */
crypto_status_t crypto_status_interpret(status_t status);

/**
 * Checks a `status_t` and returns a `crypto_status_t` on error.
 *
 * This is equvalent to `HARDENED_TRY` except that in the error case, it
 * converts the error to `crypto_status_t` before returning.
 *
 * @param expr_ An expression that evaluates to a `status_t`.
 * @return The enclosed OK value.
 */
#define OTCRYPTO_TRY_INTERPRET(expr_)                       \
  ({                                                        \
    status_t status_ = expr_;                               \
    if (hardened_status_ok(status_) != kHardenedBoolTrue) { \
      return crypto_status_interpret(status_);              \
    }                                                       \
    HARDENED_CHECK_EQ(status_.value, kHardenedBoolTrue);    \
    status_.value;                                          \
  })

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
