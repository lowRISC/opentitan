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
#include "cryptoc/sha384.h"

#include <stdint.h>
#include <string.h>

#include "cryptoc/sha512.h"

#ifndef SHA512_SUPPORT
#error "-DSHA512_SUPPORT must be specified to enable SHA-384/512"
#endif

static const HASH_VTAB SHA384_VTAB = {
  SHA384_init,
  SHA512_update,
  SHA512_final,
  SHA384_hash,
  SHA384_DIGEST_SIZE
};

void SHA384_init(LITE_SHA384_CTX* ctx) {
  ctx->f = &SHA384_VTAB;
  ctx->state[0] = 0xcbbb9d5dc1059ed8ll;
  ctx->state[1] = 0x629a292a367cd507ll;
  ctx->state[2] = 0x9159015a3070dd17ll;
  ctx->state[3] = 0x152fecd8f70e5939ll;
  ctx->state[4] = 0x67332667ffc00b31ll;
  ctx->state[5] = 0x8eb44a8768581511ll;
  ctx->state[6] = 0xdb0c2e0d64f98fa7ll;
  ctx->state[7] = 0x47b5481dbefa4fa4ll;
  ctx->count = 0;
}

void SHA384_update(LITE_SHA384_CTX* ctx, const void* data, size_t len) {
  SHA512_update(ctx, data, len);
}

const uint8_t* SHA384_final(LITE_SHA384_CTX* ctx) {
  return SHA512_final(ctx);
}

const uint8_t* SHA384_hash(const void* data, size_t len, uint8_t* digest) {
  LITE_SHA384_CTX ctx;
  SHA384_init(&ctx);
  SHA384_update(&ctx, data, len);
  memcpy(digest, SHA384_final(&ctx), SHA384_DIGEST_SIZE);
  return digest;
}
