// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/integrity_check.h"

#include "sw/device/lib/base/hardened.h"

hardened_bool_t unblinded_key_integrity_check(
    const crypto_unblinded_key_t *key) {
  // TODO: decide on a checksum algorithm and implement integrity checks.
  return kHardenedBoolTrue;
}

hardened_bool_t blinded_key_integrity_check(const crypto_blinded_key_t *key) {
  // TODO: decide on a checksum algorithm and implement integrity checks.
  return kHardenedBoolTrue;
}
