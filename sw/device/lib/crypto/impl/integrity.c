// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/integrity.h"

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/cryptolib_build_info.h"
#include "sw/device/lib/crypto/impl/state.h"

uint32_t otcrypto_integrity_unblinded_checksum(
    const otcrypto_unblinded_key_t *key) {
  if (locked_state_check().value < 0) {
    return 0;
  }
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add32(&ctx, key->key_mode);
  crc32_add32(&ctx, key->key_length);
  crc32_add(&ctx, (unsigned char *)key->key, key->key_length);
  return crc32_finish(&ctx);
}

uint32_t otcrypto_integrity_blinded_checksum(
    const otcrypto_blinded_key_t *key) {
  if (locked_state_check().value < 0) {
    return 0;
  }
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add32(&ctx, key->config.version);
  crc32_add32(&ctx, key->config.key_mode);
  crc32_add32(&ctx, key->config.key_length);
  crc32_add32(&ctx, key->config.hw_backed);
  crc32_add32(&ctx, key->config.keymgr_dpe_slot_idx);
  crc32_add32(&ctx, key->config.exportable);
  crc32_add32(&ctx, key->config.security_level);
  crc32_add32(&ctx, key->keyblob_length);
  crc32_add(&ctx, (unsigned char *)key->keyblob, key->keyblob_length);
  return crc32_finish(&ctx);
}

hardened_bool_t otcrypto_integrity_unblinded_key_check(
    const otcrypto_unblinded_key_t *key) {
  if (locked_state_check().value < 0) {
    return kHardenedBoolFalse;
  }
  if (key->checksum == launder32(otcrypto_integrity_unblinded_checksum(key))) {
    HARDENED_CHECK_EQ(key->checksum,
                      otcrypto_integrity_unblinded_checksum(key));
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}

hardened_bool_t otcrypto_integrity_blinded_key_check(
    const otcrypto_blinded_key_t *key) {
  if (locked_state_check().value < 0) {
    return kHardenedBoolFalse;
  }
  if (launder32((uint32_t)key->config.version) != (uint32_t)kCryptoLibVersion) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(key->config.version, kCryptoLibVersion);
  if (key->checksum == launder32(otcrypto_integrity_blinded_checksum(key))) {
    HARDENED_CHECK_EQ(key->checksum, otcrypto_integrity_blinded_checksum(key));
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}

#ifndef OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS

OT_NOINLINE
hardened_bool_t verify_buf_integrity(const otcrypto_generic_buf_t *buf) {
  uint32_t expected = kOtcryptoInitIntegrityChecksum +
                      (uint32_t)(uintptr_t)buf->data + (uint32_t)buf->len;

  if (buf->ptr_checksum == launder32(expected)) {
    HARDENED_CHECK_EQ(buf->ptr_checksum, expected);
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}
#endif  // OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS

typedef union {
  otcrypto_generic_buf_t generic;
  otcrypto_byte_buf_t byte_buf;
  otcrypto_const_byte_buf_t const_byte_buf;
  otcrypto_word32_buf_t word32_buf;
  otcrypto_const_word32_buf_t const_word32_buf;
} buf_union_t;

static buf_union_t make_buf_locked(const void *data, size_t len) {
  if (locked_state_check().value < 0) {
    return (buf_union_t){
        .generic = {.data = NULL, .len = 0, .ptr_checksum = 0}};
  }
  return (buf_union_t){
      .generic = OTCRYPTO_MAKE_BUF(otcrypto_generic_buf_t, (void *)data, len)};
}

otcrypto_byte_buf_t otcrypto_make_byte_buf(uint8_t *data, size_t len) {
  return make_buf_locked(data, len).byte_buf;
}

otcrypto_const_byte_buf_t otcrypto_make_const_byte_buf(const uint8_t *data,
                                                       size_t len) {
  return make_buf_locked(data, len).const_byte_buf;
}

otcrypto_word32_buf_t otcrypto_make_word32_buf(uint32_t *data, size_t len) {
  return make_buf_locked(data, len).word32_buf;
}

otcrypto_const_word32_buf_t otcrypto_make_const_word32_buf(const uint32_t *data,
                                                           size_t len) {
  return make_buf_locked(data, len).const_word32_buf;
}

static hardened_bool_t check_buf_locked(const otcrypto_generic_buf_t *buf) {
  if (locked_state_check().value < 0) {
    return kHardenedBoolFalse;
  }
  return OTCRYPTO_CHECK_BUF(buf);
}

hardened_bool_t otcrypto_check_byte_buf(const otcrypto_byte_buf_t *buf) {
  return check_buf_locked((const otcrypto_generic_buf_t *)buf);
}

hardened_bool_t otcrypto_check_const_byte_buf(
    const otcrypto_const_byte_buf_t *buf) {
  return check_buf_locked((const otcrypto_generic_buf_t *)buf);
}

hardened_bool_t otcrypto_check_word32_buf(const otcrypto_word32_buf_t *buf) {
  return check_buf_locked((const otcrypto_generic_buf_t *)buf);
}

hardened_bool_t otcrypto_check_const_word32_buf(
    const otcrypto_const_word32_buf_t *buf) {
  return check_buf_locked((const otcrypto_generic_buf_t *)buf);
}
