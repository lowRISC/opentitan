// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/integrity.h"

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"

uint32_t integrity_unblinded_checksum(const otcrypto_unblinded_key_t *key) {
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add32(&ctx, key->key_mode);
  crc32_add32(&ctx, key->key_length);
  crc32_add(&ctx, (unsigned char *)key->key, key->key_length);
  return crc32_finish(&ctx);
}

uint32_t integrity_blinded_checksum(const otcrypto_blinded_key_t *key) {
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add32(&ctx, key->config.version);
  crc32_add32(&ctx, key->config.key_mode);
  crc32_add32(&ctx, key->config.key_length);
  crc32_add32(&ctx, key->config.hw_backed);
  crc32_add32(&ctx, key->config.exportable);
  crc32_add32(&ctx, key->config.security_level);
  crc32_add32(&ctx, key->keyblob_length);
  crc32_add(&ctx, (unsigned char *)key->keyblob, key->keyblob_length);
  return crc32_finish(&ctx);
}

hardened_bool_t integrity_unblinded_key_check(
    const otcrypto_unblinded_key_t *key) {
  if (key->checksum == launder32(integrity_unblinded_checksum(key))) {
    HARDENED_CHECK_EQ(key->checksum, integrity_unblinded_checksum(key));
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}

hardened_bool_t integrity_blinded_key_check(const otcrypto_blinded_key_t *key) {
  // Reject keys that come from a newer version of the library (downgrade
  // protection).
  if (launder32(key->config.version) != kOtcryptoLibVersion1) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(key->config.version, kOtcryptoLibVersion1);

  if (key->checksum == launder32(integrity_blinded_checksum(key))) {
    HARDENED_CHECK_EQ(key->checksum, integrity_blinded_checksum(key));
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}
