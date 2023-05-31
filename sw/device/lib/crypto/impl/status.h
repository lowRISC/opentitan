// Copyright lowRISC contributors.
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

#define OTCRYPTO_RECOV_ERR ((status_t){.value = kCryptoStatusInternalError})
#define OTCRYPTO_FATAL_ERR ((status_t){.value = kCryptoStatusFatalError})
#define OTCRYPTO_BAD_ARGS ((status_t){.value = kCryptoStatusBadArgs})
#define OTCRYPTO_ASYNC_INCOMPLETE \
  ((status_t){.value = kCryptoStatusAsyncIncomplete})
#define OTCRYPTO_NOT_IMPLEMENTED \
  ((status_t){.value = kCryptoStatusNotImplemented})

#endif

/**
 * Hardened version of the `TRY` macro from `status.h`.
 *
 * Returns the error unmodified if `status_ok` fails, and throws a
 * fatal error if the OK code does not match the hardened value.
 *
 * @param expr_ An expression that evaluates to a `status_t`.
 * @return The enclosed OK value.
 */
#define HARDENED_TRY(expr_)                                           \
  ({                                                                  \
    status_t status_ = expr_;                                         \
    if (!status_ok(status_)) {                                        \
      return status_;                                                 \
    }                                                                 \
    if (launder32(OT_UNSIGNED(status_.value)) != kHardenedBoolTrue) { \
      return OTCRYPTO_FATAL_ERR;                                      \
    }                                                                 \
    HARDENED_CHECK_EQ(status_.value, kHardenedBoolTrue);              \
    status_.value;                                                    \
  })

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
