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
#include <assert.h>
#include <stdint.h>
#include <string.h>

#include "cryptoc/p256.h"

const p256_int SECP256r1_n =  // curve order
  {{0xfc632551, 0xf3b9cac2, 0xa7179e84, 0xbce6faad, -1, -1, 0, -1}};

const p256_int SECP256r1_nMin2 =  // curve order - 2
  {{0xfc632551 - 2, 0xf3b9cac2, 0xa7179e84, 0xbce6faad, -1, -1, 0, -1}};

const p256_int SECP256r1_p =  // curve field size
  {{-1, -1, -1, 0, 0, 0, 1, -1 }};

const p256_int SECP256r1_b =  // curve b
  {{0x27d2604b, 0x3bce3c3e, 0xcc53b0f6, 0x651d06b0,
    0x769886bc, 0xb3ebbd55, 0xaa3a93e7, 0x5ac635d8}};

static const p256_int p256_one = P256_ONE;


void p256_init(p256_int* a) {
  memset(a, 0, sizeof(*a));
}

void p256_clear(p256_int* a) { p256_init(a); }

int p256_get_bit(const p256_int* scalar, int bit) {
  return (P256_DIGIT(scalar, bit / P256_BITSPERDIGIT)
              >> (bit & (P256_BITSPERDIGIT - 1))) & 1;
}

int p256_is_zero(const p256_int* a) {
  int i, result = 0;
  for (i = 0; i < P256_NDIGITS; ++i) result |= P256_DIGIT(a, i);
  return !result;
}

// top, c[] += a[] * b
// Returns new top
static p256_digit mulAdd(const p256_int* a,
                         p256_digit b,
                         p256_digit top,
                         p256_digit* c) {
  int i;
  p256_ddigit carry = 0;

  for (i = 0; i < P256_NDIGITS; ++i) {
    carry += *c;
    carry += (p256_ddigit)P256_DIGIT(a, i) * b;
    *c++ = (p256_digit)carry;
    carry >>= P256_BITSPERDIGIT;
  }
  return top + (p256_digit)carry;
}

// top, c[] -= top_a, a[]
static p256_digit subTop(p256_digit top_a,
                         const p256_digit* a,
                         p256_digit top_c,
                         p256_digit* c) {
  int i;
  p256_sddigit borrow = 0;

  for (i = 0; i < P256_NDIGITS; ++i) {
    borrow += *c;
    borrow -= *a++;
    *c++ = (p256_digit)borrow;
    borrow >>= P256_BITSPERDIGIT;
  }
  borrow += top_c;
  borrow -= top_a;
  top_c = (p256_digit)borrow;
  assert((borrow >> P256_BITSPERDIGIT) == 0);
  return top_c;
}

// top, c[] -= MOD[] & mask (0 or -1)
// returns new top.
static p256_digit subM(const p256_int* MOD,
                       p256_digit top,
                       p256_digit* c,
                       p256_digit mask) {
  int i;
  p256_sddigit borrow = 0;
  for (i = 0; i < P256_NDIGITS; ++i) {
    borrow += *c;
    borrow -= P256_DIGIT(MOD, i) & mask;
    *c++ = (p256_digit)borrow;
    borrow >>= P256_BITSPERDIGIT;
  }
  return top + (p256_digit)borrow;
}

// top, c[] += MOD[] & mask (0 or -1)
// returns new top.
static p256_digit addM(const p256_int* MOD,
                       p256_digit top,
                       p256_digit* c,
                       p256_digit mask) {
  int i;
  p256_ddigit carry = 0;
  for (i = 0; i < P256_NDIGITS; ++i) {
    carry += *c;
    carry += P256_DIGIT(MOD, i) & mask;
    *c++ = (p256_digit)carry;
    carry >>= P256_BITSPERDIGIT;
  }
  return top + (p256_digit)carry;
}

// c = a * b mod MOD. c can be a and/or b.
void p256_modmul(const p256_int* MOD,
                 const p256_int* a,
                 const p256_digit top_b,
                 const p256_int* b,
                 p256_int* c) {
  p256_digit tmp[P256_NDIGITS * 2 + 1] = { 0 };
  p256_digit top = 0;
  int i;

  // Multiply/add into tmp.
  for (i = 0; i < P256_NDIGITS; ++i) {
    if (i) tmp[i + P256_NDIGITS - 1] = top;
    top = mulAdd(a, P256_DIGIT(b, i), 0, tmp + i);
  }

  // Multiply/add top digit
  tmp[i + P256_NDIGITS - 1] = top;
  top = mulAdd(a, top_b, 0, tmp + i);

  // Reduce tmp, digit by digit.
  for (; i >= 0; --i) {
    p256_digit reducer[P256_NDIGITS] = { 0 };
    p256_digit top_reducer;

    // top can be any value at this point.
    // Guestimate reducer as top * MOD, since msw of MOD is -1.
    top_reducer = mulAdd(MOD, top, 0, reducer);

    // Subtract reducer from top | tmp.
    top = subTop(top_reducer, reducer, top, tmp + i);

    // top is now either 0 or 1. Make it 0, fixed-timing.
    assert(top <= 1);

    top = subM(MOD, top, tmp + i, ~(top - 1));

    assert(top == 0);

    // We have now reduced the top digit off tmp. Fetch new top digit.
    top = tmp[i + P256_NDIGITS - 1];
  }

  // tmp might still be larger than MOD, yet same bit length.
  // Make sure it is less, fixed-timing.
  addM(MOD, 0, tmp, subM(MOD, 0, tmp, -1));

  memcpy(c, tmp, P256_NBYTES);
}

int p256_is_odd(const p256_int* a) { return P256_DIGIT(a, 0) & 1; }
int p256_is_even(const p256_int* a) { return !(P256_DIGIT(a, 0) & 1); }

p256_digit p256_shl(const p256_int* a, int n, p256_int* b) {
  int i;
  p256_digit top = P256_DIGIT(a, P256_NDIGITS - 1);

  n %= P256_BITSPERDIGIT;
  for (i = P256_NDIGITS - 1; i > 0; --i) {
    p256_digit accu = (P256_DIGIT(a, i) << n);
    accu |= (P256_DIGIT(a, i - 1) >> (P256_BITSPERDIGIT - n));
    P256_DIGIT(b, i) = accu;
  }
  P256_DIGIT(b, i) = (P256_DIGIT(a, i) << n);

  top >>= (P256_BITSPERDIGIT - n);

  return top;
}

void p256_shr(const p256_int* a, int n, p256_int* b) {
  int i;

  n %= P256_BITSPERDIGIT;
  for (i = 0; i < P256_NDIGITS - 1; ++i) {
    p256_digit accu = (P256_DIGIT(a, i) >> n);
    accu |= (P256_DIGIT(a, i + 1) << (P256_BITSPERDIGIT - n));
    P256_DIGIT(b, i) = accu;
  }
  P256_DIGIT(b, i) = (P256_DIGIT(a, i) >> n);
}

static void p256_shr1(const p256_int* a, int highbit, p256_int* b) {
  int i;

  for (i = 0; i < P256_NDIGITS - 1; ++i) {
    p256_digit accu = (P256_DIGIT(a, i) >> 1);
    accu |= (P256_DIGIT(a, i + 1) << (P256_BITSPERDIGIT - 1));
    P256_DIGIT(b, i) = accu;
  }
  P256_DIGIT(b, i) = (P256_DIGIT(a, i) >> 1) |
      (highbit << (P256_BITSPERDIGIT - 1));
}

// Return -1, 0, 1 for a < b, a == b or a > b respectively.
int p256_cmp(const p256_int* a, const p256_int* b) {
  int i;
  p256_sddigit borrow = 0;
  p256_digit notzero = 0;

  for (i = 0; i < P256_NDIGITS; ++i) {
    borrow += (p256_sddigit)P256_DIGIT(a, i) - P256_DIGIT(b, i);
    // Track whether any result digit is ever not zero.
    // Relies on !!(non-zero) evaluating to 1, e.g., !!(-1) evaluating to 1.
    notzero |= !!((p256_digit)borrow);
    borrow >>= P256_BITSPERDIGIT;
  }
  return (int)borrow | notzero;
}

// c = a - b. Returns borrow: 0 or -1.
int p256_sub(const p256_int* a, const p256_int* b, p256_int* c) {
  int i;
  p256_sddigit borrow = 0;

  for (i = 0; i < P256_NDIGITS; ++i) {
    borrow += (p256_sddigit)P256_DIGIT(a, i) - P256_DIGIT(b, i);
    if (c) P256_DIGIT(c, i) = (p256_digit)borrow;
    borrow >>= P256_BITSPERDIGIT;
  }
  return (int)borrow;
}

// c = a + b. Returns carry: 0 or 1.
int p256_add(const p256_int* a, const p256_int* b, p256_int* c) {
  int i;
  p256_ddigit carry = 0;

  for (i = 0; i < P256_NDIGITS; ++i) {
    carry += (p256_ddigit)P256_DIGIT(a, i) + P256_DIGIT(b, i);
    if (c) P256_DIGIT(c, i) = (p256_digit)carry;
    carry >>= P256_BITSPERDIGIT;
  }
  return (int)carry;
}

// b = a + d. Returns carry, 0 or 1.
int p256_add_d(const p256_int* a, p256_digit d, p256_int* b) {
  int i;
  p256_ddigit carry = d;

  for (i = 0; i < P256_NDIGITS; ++i) {
    carry += (p256_ddigit)P256_DIGIT(a, i);
    if (b) P256_DIGIT(b, i) = (p256_digit)carry;
    carry >>= P256_BITSPERDIGIT;
  }
  return (int)carry;
}

// if (mask) dst = src, fixed-timing style.
static void copyConditional(const p256_int* src,
                            p256_int* dst,
                            int mask) {
  int i;
  for (i = 0; i < P256_NDIGITS; ++i) {
    p256_digit b = P256_DIGIT(src, i) & mask;  // 0 or src[i]
    b |= P256_DIGIT(dst, i) & ~mask;  // dst[i] or 0
    P256_DIGIT(dst, i) = b;
  }
}

// -1 iff (x&15) == 0, 0 otherwise.
// Relies on arithmetic shift right behavior.
#define ZEROtoONES(x) (((int32_t)(((x)&15)-1))>>31)

// tbl[0] = tbl[idx], fixed-timing style.
static void set0ToIdx(p256_int tbl[16], int idx) {
  int32_t i;
  tbl[0] = p256_one;
  for (i = 1; i < 16; ++i) {
    copyConditional(&tbl[i], &tbl[0], ZEROtoONES(i-idx));
  }
}

// b = 1/a mod MOD, fixed timing, Fermat's little theorem.
void p256_modinv(const p256_int* MOD,
                 const p256_int* a,
                 p256_int* b) {
  p256_int tbl[16];
  int i;

  // tbl[i] = a**i, tbl[0] unused.
  tbl[1] = *a;
  for (i = 2; i < 16; ++i) {
    p256_modmul(MOD, &tbl[i-1], 0, a, &tbl[i]);
  }

  *b = p256_one;
  for (i = 256; i > 0; i -= 4) {
    int32_t idx = 0;
    p256_modmul(MOD, b, 0, b, b);
    p256_modmul(MOD, b, 0, b, b);
    p256_modmul(MOD, b, 0, b, b);
    p256_modmul(MOD, b, 0, b, b);
    idx |= p256_get_bit(&SECP256r1_nMin2, i - 1) << 3;
    idx |= p256_get_bit(&SECP256r1_nMin2, i - 2) << 2;
    idx |= p256_get_bit(&SECP256r1_nMin2, i - 3) << 1;
    idx |= p256_get_bit(&SECP256r1_nMin2, i - 4) << 0;
    set0ToIdx(tbl, idx);  // tbl[0] = tbl[idx]
    p256_modmul(MOD, b, 0, &tbl[0], &tbl[0]);
    copyConditional(&tbl[0], b, ~ZEROtoONES(idx));
  }
}

// b = 1/a mod MOD, binary euclid.
void p256_modinv_vartime(const p256_int* MOD,
                         const p256_int* a,
                         p256_int* b) {
  p256_int R = P256_ZERO;
  p256_int S = P256_ONE;
  p256_int U = *MOD;
  p256_int V = *a;

  for (;;) {
    if (p256_is_even(&U)) {
      p256_shr1(&U, 0, &U);
      if (p256_is_even(&R)) {
        p256_shr1(&R, 0, &R);
      } else {
        // R = (R+MOD)/2
        p256_shr1(&R, p256_add(&R, MOD, &R), &R);
      }
    } else if (p256_is_even(&V)) {
      p256_shr1(&V, 0, &V);
      if (p256_is_even(&S)) {
        p256_shr1(&S, 0, &S);
      } else {
        // S = (S+MOD)/2
        p256_shr1(&S, p256_add(&S, MOD, &S) , &S);
      }
    } else {  // U,V both odd.
      if (!p256_sub(&V, &U, NULL)) {
        p256_sub(&V, &U, &V);
        if (p256_sub(&S, &R, &S)) p256_add(&S, MOD, &S);
        if (p256_is_zero(&V)) break;  // done.
      } else {
        p256_sub(&U, &V, &U);
        if (p256_sub(&R, &S, &R)) p256_add(&R, MOD, &R);
      }
    }
  }

  p256_mod(MOD, &R, b);
}

void p256_mod(const p256_int* MOD,
              const p256_int* in,
              p256_int* out) {
  if (out != in) *out = *in;
  addM(MOD, 0, P256_DIGITS(out), subM(MOD, 0, P256_DIGITS(out), -1));
}

// Verify y^2 == x^3 - 3x + b mod p
// and 0 < x < p and 0 < y < p
int p256_is_valid_point(const p256_int* x, const p256_int* y) {
  p256_int y2, x3;

  if (p256_cmp(&SECP256r1_p, x) <= 0 ||
      p256_cmp(&SECP256r1_p, y) <= 0 ||
      p256_is_zero(x) ||
      p256_is_zero(y)) return 0;

  p256_modmul(&SECP256r1_p, y, 0, y, &y2);  // y^2

  p256_modmul(&SECP256r1_p, x, 0, x, &x3);  // x^2
  p256_modmul(&SECP256r1_p, x, 0, &x3, &x3);  // x^3
  if (p256_sub(&x3, x, &x3)) p256_add(&x3, &SECP256r1_p, &x3);  // x^3 - x
  if (p256_sub(&x3, x, &x3)) p256_add(&x3, &SECP256r1_p, &x3);  // x^3 - 2x
  if (p256_sub(&x3, x, &x3)) p256_add(&x3, &SECP256r1_p, &x3);  // x^3 - 3x
  if (p256_add(&x3, &SECP256r1_b, &x3))  // x^3 - 3x + b
    p256_sub(&x3, &SECP256r1_p, &x3);
  if (p256_sub(&x3, &SECP256r1_p, &x3))  // make sure 0 <= x3 < p
    p256_add(&x3, &SECP256r1_p, &x3);

  return p256_cmp(&y2, &x3) == 0;
}

void p256_from_bin(const uint8_t src[P256_NBYTES], p256_int* dst) {
  int i;
  const uint8_t* p = &src[0];

  for (i = P256_NDIGITS - 1; i >= 0; --i) {
    P256_DIGIT(dst, i) =
        (p[0] << 24) |
        (p[1] << 16) |
        (p[2] << 8) |
        p[3];
    p += 4;
  }
}

void p256_to_bin(const p256_int* src, uint8_t dst[P256_NBYTES]) {
  int i;
  uint8_t* p = &dst[0];

  for (i = P256_NDIGITS - 1; i >= 0; --i) {
    p256_digit digit = P256_DIGIT(src, i);
    p[0] = (uint8_t)(digit >> 24);
    p[1] = (uint8_t)(digit >> 16);
    p[2] = (uint8_t)(digit >> 8);
    p[3] = (uint8_t)(digit);
    p += 4;
  }
}
