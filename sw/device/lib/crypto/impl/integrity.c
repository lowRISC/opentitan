// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/integrity.h"

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"

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

#ifndef OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS
OT_NOINLINE
hardened_bool_t verify_buf_integrity(const otcrypto_generic_buf_t *buf) {
  uint32_t expected = calculate_buf_checksum(buf->data, buf->len);

  if (buf->ptr_checksum == launder32(expected)) {
    HARDENED_CHECK_EQ(buf->ptr_checksum, expected);
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}
#endif  // OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS

otcrypto_byte_buf_t otcrypto_make_byte_buf(uint8_t *data, size_t len) {
  return OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, data, len);
}

otcrypto_const_byte_buf_t otcrypto_make_const_byte_buf(const uint8_t *data,
                                                       size_t len) {
  return OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, data, len);
}
otcrypto_word32_buf_t otcrypto_make_word32_buf(uint32_t *data, size_t len) {
  return OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, data, len);
}

otcrypto_const_word32_buf_t otcrypto_make_const_word32_buf(const uint32_t *data,
                                                           size_t len) {
  return OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, data, len);
}

hardened_bool_t otcrypto_check_byte_buf(const otcrypto_byte_buf_t *buf) {
  return OTCRYPTO_CHECK_BUF(buf);
}

hardened_bool_t otcrypto_check_const_byte_buf(
    const otcrypto_const_byte_buf_t *buf) {
  return OTCRYPTO_CHECK_BUF(buf);
}

hardened_bool_t otcrypto_check_word32_buf(const otcrypto_word32_buf_t *buf) {
  return OTCRYPTO_CHECK_BUF(buf);
}

hardened_bool_t otcrypto_check_const_word32_buf(
    const otcrypto_const_word32_buf_t *buf) {
  return OTCRYPTO_CHECK_BUF(buf);
}
