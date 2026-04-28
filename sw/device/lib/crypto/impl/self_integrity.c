// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"

#ifdef HASH_SELF_CHECK_ENABLE

extern const uint8_t _libotcrypto_start_[];
extern const uint8_t _libotcrypto_end_[];
extern const uint8_t _libotcrypto_hash_[];

otcrypto_status_t otcrypto_integrity_check(void) {
  const size_t lib_len = (size_t)(_libotcrypto_end_ - _libotcrypto_start_);

  uint32_t digest_content[12] = {0};
  otcrypto_sha2_context_t ctx;
  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha384,
      .len = ARRAYSIZE(digest_content),
      .data = digest_content,
  };

  HARDENED_TRY(otcrypto_sha2_init(kOtcryptoHashModeSha384, &ctx));

  // _libotcrypto_start_ evaluates to 0 = NULL, which the API does not accept.
  // We hash the first byte from the stack to bypass it.
  uint8_t first_byte = _libotcrypto_start_[0];
  otcrypto_const_byte_buf_t first_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &first_byte, 1);
  HARDENED_TRY(otcrypto_sha2_update(&ctx, &first_buf));

  size_t acc_len = 1;
  const size_t kMaxChunkSize = 2048;

  while (acc_len < lib_len) {
    size_t len = lib_len - acc_len;
    if (len > kMaxChunkSize) {
      len = kMaxChunkSize;
    }

    otcrypto_const_byte_buf_t buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t,
        (const uint8_t *)(_libotcrypto_start_ + acc_len), len);

    HARDENED_TRY(otcrypto_sha2_update(&ctx, &buf));
    acc_len += len;
  }

  HARDENED_TRY(otcrypto_sha2_final(&ctx, &digest));

  uint32_t diff = 0;
  for (size_t i = 0; i < 48; i++) {
    diff |= ((uint8_t *)digest.data)[i] ^ _libotcrypto_hash_[i];
  }

  if (diff != 0) {
    return OTCRYPTO_FATAL_ERR;
  }

  return OTCRYPTO_OK;
}

#else

otcrypto_status_t otcrypto_integrity_check(void) { return OTCRYPTO_OK; }

#endif
