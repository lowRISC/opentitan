// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/status.h"

#include "sw/device/lib/base/hardened_status.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

crypto_status_t crypto_status_interpret(status_t status) {
  // Force the error bit to 1 if `hardened_status_ok` does not pass. Cryptolib
  // status codes are bit-compatible with `status_t`, so we can simply cast the
  // `value` parameter and return.
  if (hardened_status_ok(status) != kHardenedBoolTrue) {
    return (crypto_status_t)(status.value | 0x80000000);
  }
  HARDENED_CHECK_EQ(status.value, kHardenedBoolTrue);
  return (crypto_status_t)status.value;
}
