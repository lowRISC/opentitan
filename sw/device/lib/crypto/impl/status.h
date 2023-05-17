// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Values in `status_t` that are guaranteed to correspond to each
 * `crypto_status_t` value.
 *
 * Note: These values bypass `status_create` to avoid having a function call in
 * error cases, where we may be under attack and complexity should be
 * minimized.
 */
#define OTCRYPTO_OK ((status_t){.value = kHardenedBoolTrue})

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

/**
 * Convert a `status_t` into a `crypto_status_t`.
 *
 * For OK statuses, this routine will only convert to `kCryptoStatusOK` if the
 * the hardened value is correct. An OK status with a different value will be
 * rejected and result in `kCryptoStatusInternalError`.
 *
 * The status mapping is as follows:
 *
 *   | status code         | cryptolib status code        |
 *   |---------------------|------------------------------|
 *   | kOk                 | kCryptoStatusOK OR           |
 *   |                     |   kCryptoStatusInternalError |
 *   | kInvalidArgument    | kCryptoStatusBadArgs         |
 *   | kUnavailable        | kCryptoStatusAsyncIncomplete |
 *   | kCancelled          | kCryptoStatusInternalError   |
 *   | kDeadlineExceeded   | kCryptoStatusInternalError   |
 *   | kNotFound           | kCryptoStatusInternalError   |
 *   | kAlreadyExists      | kCryptoStatusInternalError   |
 *   | kPermissionDenied   | kCryptoStatusInternalError   |
 *   | kResourceExhausted  | kCryptoStatusInternalError   |
 *   | kAborted            | kCryptoStatusInternalError   |
 *   | kOutOfRange         | kCryptoStatusInternalError   |
 *   | kUnimplemented      | kCryptoStatusNotImplemented  |
 *   | kUnauthenticated    | kCryptoStatusInternalError   |
 *   | kUnknown            | kCryptoStatusFatalError      |
 *   | kFailedPrecondition | kCryptoStatusFatalError      |
 *   | kInternal           | kCryptoStatusFatalError      |
 *   | kDataLoss           | kCryptoStatusFatalError      |
 *
 * @param status Initial `status_t` value.
 * @return Equivalent `crypto_status_t` error code.
 */
crypto_status_t crypto_status_interpret(status_t status);

/**
 * Hardened version of the `TRY` macro from `status.h`.
 *
 * Returns the error unmodified if `status_ok` fails, and throws a
 * fatal error if the OK code does not match the hardened value.
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
      return OTCRYPTO_FATAL_ERR;                         \
    }                                                    \
    HARDENED_CHECK_EQ(status_.value, kHardenedBoolTrue); \
    status_.value;                                       \
  })

/**
 * Checks a `status_t` and returns a `crypto_status_t` on error.
 *
 * This is equvalent to `HARDENED_TRY` except that in the error case, it
 * converts the error to `crypto_status_t` before returning.
 *
 * @param expr_ An expression that evaluates to a `status_t`.
 * @return The enclosed OK value.
 */
#define OTCRYPTO_TRY_INTERPRET(expr_)                    \
  ({                                                     \
    status_t status_ = expr_;                            \
    if (launder32(status_.value) != kHardenedBoolTrue) { \
      return crypto_status_interpret(status_);           \
    }                                                    \
    HARDENED_CHECK_EQ(status_.value, kHardenedBoolTrue); \
    status_.value;                                       \
  })

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
