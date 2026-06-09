// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/integrity.h"

#ifdef FIPS_MODE

extern const uint8_t _libotcrypto_start_[];
extern const uint8_t _libotcrypto_end_[];

otcrypto_status_t otcrypto_integrity_check(void) {
  crypto_state_t *state = NULL;

  HARDENED_TRY(read_state_pointer(&state));

  if (state->locked_state == kHardenedBoolTrue) {
    return OTCRYPTO_FATAL_ERR;
  }

  const size_t lib_len = (size_t)(_libotcrypto_end_ - _libotcrypto_start_);

  uint32_t digest_content[12] = {0};
  hmac_ctx_t ctx;
  otcrypto_word32_buf_t digest = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, digest_content, ARRAYSIZE(digest_content));

  // Initialize the HMAC driver in SHA384 mode.
  hmac_hash_sha384_init(&ctx);

  size_t acc_len = 0;
  const size_t kMaxChunkSize = 2048;

  while (acc_len < lib_len) {
    size_t len = lib_len - acc_len;
    if (len > kMaxChunkSize) {
      len = kMaxChunkSize;
    }

    otcrypto_const_byte_buf_t buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t,
        (const uint8_t *)(_libotcrypto_start_ + acc_len), len);

    HARDENED_TRY(hmac_update(&ctx, &buf));
    acc_len += len;
  }

  HARDENED_TRY(hmac_final(&ctx, &digest));
  extern const uint8_t _libotcrypto_hash_[];
  const uint8_t *hash_ptr = _libotcrypto_hash_;

  uint32_t diff = 0;
  for (size_t i = 0; i < 48; i++) {
    diff |= ((uint8_t *)digest.data)[i] ^ hash_ptr[i];
  }

  if (diff != 0) {
    // Lock the cryptolib if the self-integrity check failed
    state->locked_state = kHardenedBoolTrue;
    return OTCRYPTO_FATAL_ERR;
  }

  // Set the stateful word that the self-integrity check is done
  state->self_check_state = kHardenedBoolTrue;
  return OTCRYPTO_OK;
}

#else

otcrypto_status_t otcrypto_integrity_check(void) { return OTCRYPTO_OK; }

#endif
