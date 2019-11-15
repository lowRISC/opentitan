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
#include <string.h>

#include "cryptoc/p256_prng.h"
#include "cryptoc/hmac.h"
#include "cryptoc/sha256.h"

static void uint64tobin(uint64_t v, uint8_t* t) {
  t[0] = (uint8_t)(v >> 56);
  t[1] = (uint8_t)(v >> 48);
  t[2] = (uint8_t)(v >> 40);
  t[3] = (uint8_t)(v >> 32);
  t[4] = (uint8_t)(v >> 24);
  t[5] = (uint8_t)(v >> 16);
  t[6] = (uint8_t)(v >> 8);
  t[7] = (uint8_t)(v);
}

// V = HMAC(K, V)
static void update_V(P256_PRNG_CTX* ctx) {
  LITE_HMAC_CTX hmac;
  HMAC_SHA256_init(&hmac, ctx->Key, P256_PRNG_SIZE);
  HMAC_update(&hmac, ctx->V, P256_PRNG_SIZE);
  memcpy(ctx->V, HMAC_final(&hmac), P256_PRNG_SIZE);
}

// K = HMAC(K, V || [0,1] || count || seed)
static void update_Key(P256_PRNG_CTX* ctx, int which,
                     const void* seed, size_t seed_size) {
  LITE_HMAC_CTX hmac;
  uint8_t tmp[16 + 1];

  HMAC_SHA256_init(&hmac, ctx->Key, P256_PRNG_SIZE);
  HMAC_update(&hmac, ctx->V, P256_PRNG_SIZE);
  tmp[0] = which;
  uint64tobin(ctx->instance_count, tmp + 1);
  uint64tobin(ctx->call_count, tmp + 8 + 1);
  HMAC_update(&hmac, tmp, sizeof(tmp));
  HMAC_update(&hmac, seed, seed_size);
  memcpy(ctx->Key, HMAC_final(&hmac), P256_PRNG_SIZE);
}

void p256_prng_add(P256_PRNG_CTX* ctx,
                   const void* seed, size_t seed_size) {
  update_Key(ctx, 0, seed, seed_size);
  update_V(ctx);
  update_Key(ctx, 1, seed, seed_size);
  update_V(ctx);
}

void p256_prng_init(P256_PRNG_CTX* ctx,
                    const void* seed, size_t seed_size,
                    uint64_t instance_count) {
  // Key = { 0 }, V = { 1 }
  memset(ctx->Key, 0, P256_PRNG_SIZE);
  memset(ctx->V, 1, P256_PRNG_SIZE);

  ctx->instance_count = instance_count;
  ctx->call_count = 0;

  p256_prng_add(ctx, seed, seed_size);
}

void p256_prng_draw(P256_PRNG_CTX* ctx, uint8_t dst[P256_PRNG_SIZE]) {
  update_V(ctx);

  // Output = V
  memcpy(dst, ctx->V, P256_PRNG_SIZE);

  ctx->call_count++;

  update_Key(ctx, 0, NULL, 0);
  update_V(ctx);
}
