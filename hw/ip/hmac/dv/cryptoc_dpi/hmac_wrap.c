// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "hmac.h"
#include "sha.h"
#include "sha256.h"

const uint8_t *HMAC_SHA(const void *key, size_t key_len, const void *msg,
                        size_t msg_len, uint8_t *hmac) {
  LITE_HMAC_CTX ctx;
  HMAC_SHA_init(&ctx, key, key_len);
  // H(msg)
  HMAC_update(&ctx, msg, msg_len);
  memcpy(hmac, HMAC_final(&ctx), SHA_DIGEST_SIZE);
  return hmac;
}

const uint8_t *HMAC_SHA256(const void *key, size_t key_len, const void *msg,
                           size_t msg_len, uint8_t *hmac) {
  LITE_HMAC_CTX ctx;
  HMAC_SHA256_init(&ctx, key, key_len);
  // H(msg)
  HMAC_update(&ctx, msg, msg_len);
  memcpy(hmac, HMAC_final(&ctx), SHA256_DIGEST_SIZE);
  return hmac;
}
