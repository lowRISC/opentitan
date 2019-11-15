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
#include "cryptoc/sha512.h"

#include <stdint.h>
#include <string.h>

#ifndef SHA512_SUPPORT
#error "-DSHA512_SUPPORT must be specified to enable SHA-384/512"
#endif

#define ror(value, bits) (((value) >> (bits)) | ((value) << (64 - (bits))))
#define shr(value, bits) ((value) >> (bits))

static const uint64_t K[80] = {
  0x428A2F98D728AE22ll, 0x7137449123EF65CDll, 0xB5C0FBCFEC4D3B2Fll,
  0xE9B5DBA58189DBBCll, 0x3956C25BF348B538ll, 0x59F111F1B605D019ll,
  0x923F82A4AF194F9Bll, 0xAB1C5ED5DA6D8118ll, 0xD807AA98A3030242ll,
  0x12835B0145706FBEll, 0x243185BE4EE4B28Cll, 0x550C7DC3D5FFB4E2ll,
  0x72BE5D74F27B896Fll, 0x80DEB1FE3B1696B1ll, 0x9BDC06A725C71235ll,
  0xC19BF174CF692694ll, 0xE49B69C19EF14AD2ll, 0xEFBE4786384F25E3ll,
  0x0FC19DC68B8CD5B5ll, 0x240CA1CC77AC9C65ll, 0x2DE92C6F592B0275ll,
  0x4A7484AA6EA6E483ll, 0x5CB0A9DCBD41FBD4ll, 0x76F988DA831153B5ll,
  0x983E5152EE66DFABll, 0xA831C66D2DB43210ll, 0xB00327C898FB213Fll,
  0xBF597FC7BEEF0EE4ll, 0xC6E00BF33DA88FC2ll, 0xD5A79147930AA725ll,
  0x06CA6351E003826Fll, 0x142929670A0E6E70ll, 0x27B70A8546D22FFCll,
  0x2E1B21385C26C926ll, 0x4D2C6DFC5AC42AEDll, 0x53380D139D95B3DFll,
  0x650A73548BAF63DEll, 0x766A0ABB3C77B2A8ll, 0x81C2C92E47EDAEE6ll,
  0x92722C851482353Bll, 0xA2BFE8A14CF10364ll, 0xA81A664BBC423001ll,
  0xC24B8B70D0F89791ll, 0xC76C51A30654BE30ll, 0xD192E819D6EF5218ll,
  0xD69906245565A910ll, 0xF40E35855771202All, 0x106AA07032BBD1B8ll,
  0x19A4C116B8D2D0C8ll, 0x1E376C085141AB53ll, 0x2748774CDF8EEB99ll,
  0x34B0BCB5E19B48A8ll, 0x391C0CB3C5C95A63ll, 0x4ED8AA4AE3418ACBll,
  0x5B9CCA4F7763E373ll, 0x682E6FF3D6B2B8A3ll, 0x748F82EE5DEFB2FCll,
  0x78A5636F43172F60ll, 0x84C87814A1F0AB72ll, 0x8CC702081A6439ECll,
  0x90BEFFFA23631E28ll, 0xA4506CEBDE82BDE9ll, 0xBEF9A3F7B2C67915ll,
  0xC67178F2E372532Bll, 0xCA273ECEEA26619Cll, 0xD186B8C721C0C207ll,
  0xEADA7DD6CDE0EB1Ell, 0xF57D4F7FEE6ED178ll, 0x06F067AA72176FBAll,
  0x0A637DC5A2C898A6ll, 0x113F9804BEF90DAEll, 0x1B710B35131C471Bll,
  0x28DB77F523047D84ll, 0x32CAAB7B40C72493ll, 0x3C9EBE0A15C9BEBCll,
  0x431D67C49C100D4Cll, 0x4CC5D4BECB3E42B6ll, 0x597F299CFC657E2All,
  0x5FCB6FAB3AD6FAECll, 0x6C44198C4A475817ll
};

static void SHA512_Transform(LITE_SHA512_CTX* ctx) {
  uint64_t W[80];
  uint64_t A, B, C, D, E, F, G, H;
  uint8_t* p = ctx->buf;
  int t;

  for(t = 0; t < 16; t++) {
    uint64_t tmp =  (uint64_t)(*p++) << 56;
    tmp |= (uint64_t)(*p++) << 48;
    tmp |= (uint64_t)(*p++) << 40;
    tmp |= (uint64_t)(*p++) << 32;
    tmp |= (uint64_t)(*p++) << 24;
    tmp |= (uint64_t)(*p++) << 16;
    tmp |= (uint64_t)(*p++) << 8;
    tmp |= (uint64_t)(*p++);
    W[t] = tmp;
  }

  for(; t < 80; t++) {
    uint64_t Wt2 = W[t - 2];
    uint64_t Wt7 = W[t - 7];
    uint64_t Wt15 = W[t - 15];
    uint64_t Wt16 = W[t - 16];

    uint64_t s0 = ror(Wt15, 1) ^ ror(Wt15, 8) ^ shr(Wt15, 7);
    uint64_t s1 = ror(Wt2, 19) ^ ror(Wt2, 61) ^ shr(Wt2, 6);

    W[t] = s1 + Wt7 + s0 + Wt16;
  }

  A = ctx->state[0];
  B = ctx->state[1];
  C = ctx->state[2];
  D = ctx->state[3];
  E = ctx->state[4];
  F = ctx->state[5];
  G = ctx->state[6];
  H = ctx->state[7];

  for(t = 0; t < 80; t++) {
    uint64_t s0 = ror(A, 28) ^ ror(A, 34) ^ ror(A, 39);
    uint64_t maj = (A & B) ^ (A & C) ^ (B & C);
    uint64_t t2 = s0 + maj;
    uint64_t s1 = ror(E, 14) ^ ror(E, 18) ^ ror(E, 41);
    uint64_t ch = (E & F) ^ ((~E) & G);
    uint64_t t1 = H + s1 + ch + K[t] + W[t];

    H = G;
    G = F;
    F = E;
    E = D + t1;
    D = C;
    C = B;
    B = A;
    A = t1 + t2;
  }

  ctx->state[0] += A;
  ctx->state[1] += B;
  ctx->state[2] += C;
  ctx->state[3] += D;
  ctx->state[4] += E;
  ctx->state[5] += F;
  ctx->state[6] += G;
  ctx->state[7] += H;
}

static const HASH_VTAB SHA512_VTAB = {
  SHA512_init,
  SHA512_update,
  SHA512_final,
  SHA512_hash,
  SHA512_DIGEST_SIZE
};

void SHA512_init(LITE_SHA512_CTX* ctx) {
  ctx->f = &SHA512_VTAB;
  ctx->state[0] = 0x6a09e667f3bcc908ll;
  ctx->state[1] = 0xbb67ae8584caa73bll;
  ctx->state[2] = 0x3c6ef372fe94f82bll;
  ctx->state[3] = 0xa54ff53a5f1d36f1ll;
  ctx->state[4] = 0x510e527fade682d1ll;
  ctx->state[5] = 0x9b05688c2b3e6c1fll;
  ctx->state[6] = 0x1f83d9abfb41bd6bll;
  ctx->state[7] = 0x5be0cd19137e2179ll;
  ctx->count = 0;
}

void SHA512_update(LITE_SHA512_CTX* ctx, const void* data, size_t len) {
  int i = (int) (ctx->count & 127);
  const uint8_t* p = (const uint8_t*)data;

  ctx->count += len;

  while (len--) {
    ctx->buf[i++] = *p++;
    if (i == 128) {
      SHA512_Transform(ctx);
      i = 0;
    }
  }
}

const uint8_t* SHA512_final(LITE_SHA512_CTX* ctx) {
  uint8_t *p = ctx->buf;
  uint64_t cnt = ctx->count * 8;
  int i;

  SHA512_update(ctx, (uint8_t*)"\x80", 1);
  while ((ctx->count & 127) != 112) {
    SHA512_update(ctx, (uint8_t*)"\0", 1);
  }
  for (i = 0; i < 8; ++i) {
    SHA512_update(ctx, (uint8_t*)"\0", 1);
  }
  for (i = 0; i < 8; ++i) {
    uint8_t tmp = (uint8_t) (cnt >> 56);
    cnt <<= 8;
    SHA512_update(ctx, &tmp, 1);
  }

  for (i = 0; i < 8; i++) {
    uint64_t tmp = ctx->state[i];
    *p++ = (uint8_t)(tmp >> 56);
    *p++ = (uint8_t)(tmp >> 48);
    *p++ = (uint8_t)(tmp >> 40);
    *p++ = (uint8_t)(tmp >> 32);
    *p++ = (uint8_t)(tmp >> 24);
    *p++ = (uint8_t)(tmp >> 16);
    *p++ = (uint8_t)(tmp >> 8);
    *p++ = (uint8_t)(tmp >> 0);
  }

  return ctx->buf;
}

/* Convenience function */
const uint8_t* SHA512_hash(const void* data, size_t len,
                           uint8_t* digest) {
  LITE_SHA512_CTX ctx;
  SHA512_init(&ctx);
  SHA512_update(&ctx, data, len);
  memcpy(digest, SHA512_final(&ctx), SHA512_DIGEST_SIZE);
  return digest;
}
