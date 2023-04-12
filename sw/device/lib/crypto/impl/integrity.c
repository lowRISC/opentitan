// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/integrity.h"

#include "sw/device/lib/base/hardened.h"

uint32_t integrity_unblinded_checksum(const crypto_unblinded_key_t *key) {
  // TODO: decide on a checksum algorithm and implement integrity checks.
  // TODO: maybe check the key length to make sure it's not pushing UINT32_MAX,
  // as an overflow protection.
  return 0;
}

uint32_t integrity_blinded_checksum(const crypto_blinded_key_t *key) {
  // TODO: decide on a checksum algorithm and implement integrity checks.
  // TODO: maybe check the key length to make sure it's not pushing UINT32_MAX,
  // as an overflow protection.
  return 0;
}

hardened_bool_t integrity_unblinded_key_check(
    const crypto_unblinded_key_t *key) {
  if (key->checksum == launder32(integrity_unblinded_checksum(key))) {
    HARDENED_CHECK_EQ(key->checksum, integrity_unblinded_checksum(key));
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}

hardened_bool_t integrity_blinded_key_check(const crypto_blinded_key_t *key) {
  if (key->checksum == launder32(integrity_blinded_checksum(key))) {
    HARDENED_CHECK_EQ(key->checksum, integrity_blinded_checksum(key));
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}
