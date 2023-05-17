// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/status.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

crypto_status_t crypto_status_interpret(status_t status) {
  // First, check for a hardened-ok status.
  if (launder32(status.value) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(status.value, kHardenedBoolTrue);
    return launder32((crypto_status_t)status.value);
  }

  switch (status_err(status)) {
    case kOk:
      // This status indicates OK but the hardened value doesn't match; return
      // an error.
      return kCryptoStatusInternalError;
    case kInvalidArgument:
      return kCryptoStatusBadArgs;
    case kUnavailable:
      return kCryptoStatusAsyncIncomplete;
    case kCancelled:
      return kCryptoStatusInternalError;
    case kDeadlineExceeded:
      return kCryptoStatusInternalError;
    case kNotFound:
      return kCryptoStatusInternalError;
    case kAlreadyExists:
      return kCryptoStatusInternalError;
    case kPermissionDenied:
      return kCryptoStatusInternalError;
    case kResourceExhausted:
      return kCryptoStatusInternalError;
    case kAborted:
      return kCryptoStatusInternalError;
    case kOutOfRange:
      return kCryptoStatusInternalError;
    case kUnimplemented:
      return kCryptoStatusNotImplemented;
    case kUnauthenticated:
      return kCryptoStatusInternalError;
    case kUnknown:
      return kCryptoStatusFatalError;
    case kFailedPrecondition:
      return kCryptoStatusFatalError;
    case kInternal:
      return kCryptoStatusFatalError;
    case kDataLoss:
      return kCryptoStatusFatalError;
    default:
      // Conservatively return a fatal error in case we encounter something
      // unexpected.
      return kCryptoStatusFatalError;
  }

  HARDENED_TRAP();
  return kCryptoStatusFatalError;
}
