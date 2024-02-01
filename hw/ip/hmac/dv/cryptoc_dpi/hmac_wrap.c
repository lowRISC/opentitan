// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "hmac.h"
#include "sha.h"
#include "sha256.h"
#include "sha384.h"
#include "sha512.h"

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
  memcpy(hmac, HMAC_final_LITE(&ctx), SHA256_DIGEST_SIZE);
  return hmac;
}

const uint8_t *HMAC_SHA384(const void *key, size_t key_len, const void *msg,
                           size_t msg_len, uint8_t *hmac) {
  HMAC_CTX ctx;
  HMAC_SHA384_init(&ctx, key, key_len);
  // H(msg)
  HMAC_update(&ctx, msg, msg_len);
  memcpy(hmac, HMAC_final(&ctx), SHA384_DIGEST_SIZE);
  return hmac;
}

const uint8_t *HMAC_SHA512(const void *key, size_t key_len, const void *msg,
                           size_t msg_len, uint8_t *hmac) {
  HMAC_CTX ctx;
  HMAC_SHA512_init(&ctx, key, key_len);
  // H(msg)
  HMAC_update(&ctx, msg, msg_len);
  memcpy(hmac, HMAC_final(&ctx), SHA512_DIGEST_SIZE);
  return hmac;
}
