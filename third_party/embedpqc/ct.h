// Copyright 1995-2016 The OpenSSL Project Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef OPENTITAN_THIRD_PARTY_EMBEDPQC_CT_H_
#define OPENTITAN_THIRD_PARTY_EMBEDPQC_CT_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef uint32_t ct_uint32_t;

static inline ct_uint32_t ct_value_barrier(ct_uint32_t x) {
  asm volatile("" : [x] "+r"(x) :);
  return x;
}

static inline ct_uint32_t ct_if(ct_uint32_t mask, ct_uint32_t a,
                                ct_uint32_t b) {
  mask = ct_value_barrier(mask);
  return (mask & a) | (~mask & b);
}

static inline ct_uint32_t ct_lt(ct_uint32_t a, ct_uint32_t b) {
  ct_uint32_t mask = a ^ ((a ^ b) | ((a - b) ^ a));
  return 0u - (mask >> (sizeof(mask) * 8 - 1));
}

static inline ct_uint32_t ct_ge(ct_uint32_t a, ct_uint32_t b) {
  return ~ct_lt(a, b);
}

// See https://www.bearssl.org/ctmul.html for more details on non-constant time
// multiplication on different CPUs.
static inline uint64_t ct_mul64(uint32_t a, uint32_t b) {
#if defined(__ARM_ARCH_6M__) || defined(__ARM_ARCH_7M__)
  uint32_t a_lo = a & 0xFFFF;
  uint32_t a_hi = a >> 16;
  uint32_t b_lo = b & 0xFFFF;
  uint32_t b_hi = b >> 16;

  uint32_t m0 = ct_value_barrier(a_lo * b_lo);
  uint32_t m1 = ct_value_barrier(a_lo * b_hi);
  uint32_t m2 = ct_value_barrier(a_hi * b_lo);
  uint32_t m3 = ct_value_barrier(a_hi * b_hi);

  uint32_t mid = (m0 >> 16) + (m1 & 0xFFFF) + (m2 & 0xFFFF);

  uint32_t res_lo = (m0 & 0xFFFF) | ((mid & 0xFFFF) << 16);
  uint32_t res_hi = m3 + (m1 >> 16) + (m2 >> 16) + (mid >> 16);

  return ((uint64_t)res_hi << 32) | res_lo;
#else
  return (uint64_t)a * b;
#endif
}

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_THIRD_PARTY_EMBEDPQC_CT_H_
