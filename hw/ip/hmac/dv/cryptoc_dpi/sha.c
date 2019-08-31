// Copyright 2016 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#include "sha.h"

#include <stdint.h>
#include <string.h>

#define rol(bits, value) (((value) << (bits)) | ((value) >> (32 - (bits))))

static void SHA1_Transform(SHA_CTX *ctx) {
  uint32_t W[80];
  uint32_t A, B, C, D, E;
  uint8_t *p = ctx->buf;
  int t;

  for (t = 0; t < 16; ++t) {
    uint32_t tmp = *p++ << 24;
    tmp |= *p++ << 16;
    tmp |= *p++ << 8;
    tmp |= *p++;
    W[t] = tmp;
  }

  for (; t < 80; t++) {
    W[t] = rol(1, W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16]);
  }

  A = ctx->state[0];
  B = ctx->state[1];
  C = ctx->state[2];
  D = ctx->state[3];
  E = ctx->state[4];

  for (t = 0; t < 80; t++) {
    uint32_t tmp = rol(5, A) + E + W[t];

    if (t < 20) {
      tmp += (D ^ (B & (C ^ D))) + 0x5A827999;
    } else if (t < 40) {
      tmp += (B ^ C ^ D) + 0x6ED9EBA1;
    } else if (t < 60) {
      tmp += ((B & C) | (D & (B | C))) + 0x8F1BBCDC;
    } else {
      tmp += (B ^ C ^ D) + 0xCA62C1D6;
    }

    E = D;
    D = C;
    C = rol(30, B);
    B = A;
    A = tmp;
  }

  ctx->state[0] += A;
  ctx->state[1] += B;
  ctx->state[2] += C;
  ctx->state[3] += D;
  ctx->state[4] += E;
}

static const HASH_VTAB SHA_VTAB = {SHA_init, SHA_update, SHA_final, SHA_hash,
                                   SHA_DIGEST_SIZE};

void SHA_init(SHA_CTX *ctx) {
  ctx->f = &SHA_VTAB;
  ctx->state[0] = 0x67452301;
  ctx->state[1] = 0xEFCDAB89;
  ctx->state[2] = 0x98BADCFE;
  ctx->state[3] = 0x10325476;
  ctx->state[4] = 0xC3D2E1F0;
  ctx->count = 0;
}

void SHA_update(SHA_CTX *ctx, const void *data, size_t len) {
  unsigned int i = (unsigned int)(ctx->count & 63);
  const uint8_t *p = (const uint8_t *)data;

  ctx->count += len;

  while (len--) {
    ctx->buf[i++] = *p++;
    if (i == 64) {
      SHA1_Transform(ctx);
      i = 0;
    }
  }
}

const uint8_t *SHA_final(SHA_CTX *ctx) {
  uint8_t *p = ctx->buf;
  uint64_t cnt = ctx->count * 8;
  int i;

  SHA_update(ctx, (uint8_t *)"\x80", 1);
  while ((ctx->count & 63) != 56) {
    SHA_update(ctx, (uint8_t *)"\0", 1);
  }
  for (i = 0; i < 8; ++i) {
    uint8_t tmp = (uint8_t)(cnt >> 56);
    cnt <<= 8;
    SHA_update(ctx, &tmp, 1);
  }

  for (i = 0; i < 5; i++) {
    uint32_t tmp = ctx->state[i];
    *p++ = (uint8_t)(tmp >> 24);
    *p++ = (uint8_t)(tmp >> 16);
    *p++ = (uint8_t)(tmp >> 8);
    *p++ = (uint8_t)(tmp >> 0);
  }

  return ctx->buf;
}

/* Convenience function */
const uint8_t *SHA_hash(const void *data, size_t len, uint8_t *digest) {
  SHA_CTX ctx;
  SHA_init(&ctx);
  SHA_update(&ctx, data, len);
  memcpy(digest, SHA_final(&ctx), SHA_DIGEST_SIZE);
  return digest;
}
