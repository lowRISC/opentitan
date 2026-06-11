// Copyright 2026 The BoringSSL Authors
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

#include "third_party/embedpqc/mldsa_tiny_common.h"

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "third_party/embedpqc/ct.h"
#include "third_party/embedpqc/shake.h"

/* Arithmetic. */

static const uint32_t kNTTRootsMontgomery[K_DEGREE] = {
    4193792, 25847,   5771523, 7861508, 237124,  7602457, 7504169, 466468,
    1826347, 2353451, 8021166, 6288512, 3119733, 5495562, 3111497, 2680103,
    2725464, 1024112, 7300517, 3585928, 7830929, 7260833, 2619752, 6271868,
    6262231, 4520680, 6980856, 5102745, 1757237, 8360995, 4010497, 280005,
    2706023, 95776,   3077325, 3530437, 6718724, 4788269, 5842901, 3915439,
    4519302, 5336701, 3574422, 5512770, 3539968, 8079950, 2348700, 7841118,
    6681150, 6736599, 3505694, 4558682, 3507263, 6239768, 6779997, 3699596,
    811944,  531354,  954230,  3881043, 3900724, 5823537, 2071892, 5582638,
    4450022, 6851714, 4702672, 5339162, 6927966, 3475950, 2176455, 6795196,
    7122806, 1939314, 4296819, 7380215, 5190273, 5223087, 4747489, 126922,
    3412210, 7396998, 2147896, 2715295, 5412772, 4686924, 7969390, 5903370,
    7709315, 7151892, 8357436, 7072248, 7998430, 1349076, 1852771, 6949987,
    5037034, 264944,  508951,  3097992, 44288,   7280319, 904516,  3958618,
    4656075, 8371839, 1653064, 5130689, 2389356, 8169440, 759969,  7063561,
    189548,  4827145, 3159746, 6529015, 5971092, 8202977, 1315589, 1341330,
    1285669, 6795489, 7567685, 6940675, 5361315, 4499357, 4751448, 3839961,
    2091667, 3407706, 2316500, 3817976, 5037939, 2244091, 5933984, 4817955,
    266997,  2434439, 7144689, 3513181, 4860065, 4621053, 7183191, 5187039,
    900702,  1859098, 909542,  819034,  495491,  6767243, 8337157, 7857917,
    7725090, 5257975, 2031748, 3207046, 4823422, 7855319, 7611795, 4784579,
    342297,  286988,  5942594, 4108315, 3437287, 5038140, 1735879, 203044,
    2842341, 2691481, 5790267, 1265009, 4055324, 1247620, 2486353, 1595974,
    4613401, 1250494, 2635921, 4832145, 5386378, 1869119, 1903435, 7329447,
    7047359, 1237275, 5062207, 6950192, 7929317, 1312455, 3306115, 6417775,
    7100756, 1917081, 5834105, 7005614, 1500165, 777191,  2235880, 3406031,
    7838005, 5548557, 6709241, 6533464, 5796124, 4656147, 594136,  4603424,
    6366809, 2432395, 2454455, 8215696, 1957272, 3369112, 185531,  7173032,
    5196991, 162844,  1616392, 3014001, 810149,  1652634, 4686184, 6581310,
    5341501, 3523897, 3866901, 269760,  2213111, 7404533, 1717735, 472078,
    7953734, 1723600, 6577327, 1910376, 6712985, 7276084, 8119771, 4546524,
    5441381, 6144432, 7959518, 6094090, 183443,  7403526, 1612842, 4834730,
    7826001, 3919660, 8332111, 7018208, 3937738, 1400424, 7534263, 1976782};

// Reduces x mod K_PRIME in constant time, where 0 <= x < 2*K_PRIME.
uint32_t reduce_once(uint32_t x) {
  // return x < K_PRIME ? x : x - K_PRIME;
  return ct_if(ct_lt(x, K_PRIME), x, x - K_PRIME);
}

// Returns the absolute value in constant time.
static uint32_t abs_signed(uint32_t x) {
  // return is_positive(x) ? x : -x;
  return ct_if(ct_lt(x, 0x80000000), x, 0u - x);
}

// Returns the absolute value modulo K_PRIME.
static uint32_t abs_mod_prime(uint32_t x) {
  // return x > K_HALF_PRIME ? K_PRIME - x : x;
  return ct_if(ct_lt(K_HALF_PRIME, x), K_PRIME - x, x);
}

// Returns the maximum of two values in constant time.
static uint32_t maximum(uint32_t x, uint32_t y) {
  // return x < y ? y : x;
  return ct_if(ct_lt(x, y), y, x);
}

uint32_t mod_sub(uint32_t a, uint32_t b) {
  return reduce_once(K_PRIME + a - b);
}

void scalar_add(scalar_t *out, const scalar_t *lhs, const scalar_t *rhs) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = reduce_once(lhs->c[i] + rhs->c[i]);
  }
}

void scalar_sub(scalar_t *out, const scalar_t *lhs, const scalar_t *rhs) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = mod_sub(lhs->c[i], rhs->c[i]);
  }
}

static uint32_t mul_montgomery(uint32_t x, uint32_t y) {
  uint64_t z = ct_mul64(x, y);
#if defined(__ARM_ARCH_6M__) || defined(__ARM_ARCH_7M__)
  uint32_t z_lo = (uint32_t)z;
  uint64_t a = -(z_lo << 26) + (z_lo << 23) - (z_lo << 13) - z_lo;
  uint64_t b = z + (a << 23) - (a << 13) + a;
#else
  uint32_t a = (uint32_t)ct_mul64((uint32_t)z, K_PRIME_NEG_INVERSE);
  uint64_t b = z + ct_mul64(a, K_PRIME);
#endif
  uint32_t c = b >> 32;
  return reduce_once(c);
}

// Multiply two scalars in NTT form.
void scalar_mul(scalar_t *out, const scalar_t *lhs, const scalar_t *rhs) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = mul_montgomery(lhs->c[i], rhs->c[i]);
  }
}

// For scalars a, b, c in NTT form, compute a + b * c.
void scalar_mul_add(scalar_t *out, const scalar_t *a, const scalar_t *b,
                    const scalar_t *c) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = reduce_once(a->c[i] + mul_montgomery(b->c[i], c->c[i]));
  }
}

// In place number theoretic transform of a given scalar.
//
// FIPS 204, Algorithm 41 (`NTT`).
void scalar_ntt(scalar_t *s) {
  // Step: 1, 2, 4, 8, ..., 128
  // Offset: 128, 64, 32, 16, ..., 1
  int offset = K_DEGREE;
  for (int step = 1; step < K_DEGREE; step <<= 1) {
    offset >>= 1;
    int k = 0;
    for (int i = 0; i < step; i++) {
      const uint32_t step_root = kNTTRootsMontgomery[step + i];
      for (int j = k; j < k + offset; j++) {
        uint32_t even = s->c[j];
        // |mul_montgomery| works on values up to K_PRIME*R and R >
        // 2*K_PRIME. |step_root| < K_PRIME because it's static data.
        // |s->c[...]| is < K_PRIME by the invariants of that struct.
        uint32_t odd = mul_montgomery(step_root, s->c[j + offset]);
        s->c[j] = reduce_once(odd + even);
        s->c[j + offset] = mod_sub(even, odd);
      }
      k += 2 * offset;
    }
  }
}

// In place inverse number theoretic transform of a given scalar.
//
// FIPS 204, Algorithm 42 (`NTT^-1`).
void scalar_inverse_ntt(scalar_t *s) {
  // Step: 128, 64, 32, 16, ..., 1
  // Offset: 1, 2, 4, 8, ..., 128
  int step = K_DEGREE;
  for (int offset = 1; offset < K_DEGREE; offset <<= 1) {
    step >>= 1;
    int k = 0;
    for (int i = 0; i < step; i++) {
      const uint32_t step_root =
          K_PRIME - kNTTRootsMontgomery[step + (step - 1 - i)];
      for (int j = k; j < k + offset; j++) {
        uint32_t even = s->c[j];
        uint32_t odd = s->c[j + offset];
        s->c[j] = reduce_once(odd + even);
        // |mul_montgomery| works on values up to K_PRIME*R and R >
        // 2*K_PRIME. K_PRIME + even < 2*K_PRIME because |even| < K_PRIME, by
        // the invariants of that structure. Thus K_PRIME + even - odd <
        // 2*K_PRIME because odd >= 0, because it's unsigned and less than
        // K_PRIME. Lastly step_root < K_PRIME, because |kNTTRootsMontgomery| is
        // static data.
        s->c[j + offset] = mul_montgomery(step_root, K_PRIME + even - odd);
      }
      k += 2 * offset;
    }
  }
  for (size_t i = 0; i < K_DEGREE; i++) {
    s->c[i] = mul_montgomery(s->c[i], K_INVERSE_DEGREE_MONTGOMERY);
  }
}

/* Rounding and hints. */

// The input vector contains only zeroes and ones.
size_t scalar_count_ones(const scalar_t *s) {
  size_t count = 0;
  for (size_t i = 0; i < K_DEGREE; i++) {
    count += s->c[i];
  }
  return count;
}

// FIPS 204, Algorithm 35 (`Power2Round`).
void power2_round(uint32_t *r1, uint32_t *r0, uint32_t r) {
  *r1 = r >> K_DROPPED_BITS;
  *r0 = r - (*r1 << K_DROPPED_BITS);

  uint32_t r0_adjusted = mod_sub(*r0, 1 << K_DROPPED_BITS);
  uint32_t r1_adjusted = *r1 + 1;

  // Mask is set iff r0 > 2^(dropped_bits - 1).
  ct_uint32_t cond = ct_lt((uint32_t)(1 << (K_DROPPED_BITS - 1)), *r0);
  // r0 = cond ? r0_adjusted : r0
  *r0 = ct_if(cond, r0_adjusted, *r0);
  // r1 = cond ? r1_adjusted : r1
  *r1 = ct_if(cond, r1_adjusted, *r1);
}

// Scale back previously rounded value.
void scale_power2_round(uint32_t *out, uint32_t r1) {
  // Pre-condition: 0 <= r1 <= 2^10 - 1
  *out = r1 << K_DROPPED_BITS;
  // Post-condition: 0 <= out <= 2^23 - 2^13 = K_PRIME - 1
}

void scalar_power2_round(scalar_t *s1, scalar_t *s0, const scalar_t *s) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    power2_round(&s1->c[i], &s0->c[i], s->c[i]);
  }
}

void scalar_scale_power2_round(scalar_t *out, const scalar_t *in) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    scale_power2_round(&out->c[i], in->c[i]);
  }
}

void scalar_max(uint32_t *max, const scalar_t *s) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    uint32_t abs = abs_mod_prime(s->c[i]);
    *max = maximum(*max, abs);
  }
}

void scalar_max_signed(uint32_t *max, const scalar_t *s) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    uint32_t abs = abs_signed(s->c[i]);
    *max = maximum(*max, abs);
  }
}

// FIPS 204, Algorithm 37 (`HighBits`), specialized to γ2 = (q - 1)/32.
static uint32_t high_bits_32(uint32_t x) {
  // Reference description (given 0 <= x < q):
  //
  // ```
  // int32_t r0 = x mod+- (2 * gamma2);
  // if (x - r0 == q - 1) {
  //   return 0;
  // } else {
  //   return (x - r0) / (2 * gamma2);
  // }
  // ```
  //
  // Below is the formula taken from the reference implementation.
  //
  // Here, gamma2 == 2^18 - 2^8
  // This returns ((ceil(x / 2^7) * (2^10 + 1) + 2^21) / 2^22) mod 2^4
  uint32_t r1 = (x + 127) >> 7;
  r1 = (r1 * 1025 + (1 << 21)) >> 22;
  r1 &= 15;
  return r1;
}

// FIPS 204, Algorithm 37 (`HighBits`), specialized to γ2 = (q - 1)/88.
static uint32_t high_bits_88(uint32_t x) {
  // Reference description (given 0 <= x < q):
  //
  // ```
  // int32_t r0 = x mod+- (2 * gamma2);
  // if (x - r0 == q - 1) {
  //   return 0;
  // } else {
  //   return (x - r0) / (2 * gamma2);
  // }
  // ```
  //
  // Below is the formula taken from the reference implementation.
  //
  uint32_t r1 = (x + 127) >> 7;
  r1 = (r1 * 11275 + (1 << 23)) >> 24;
  r1 ^= (uint32_t)((43 - (int32_t)r1) >> 31) & r1;
  return r1;
}

// FIPS 204, Algorithm 36 (`Decompose`), specialized to γ2 = (q - 1)/32.
static void decompose_32(uint32_t *r1, int32_t *r0, uint32_t r) {
  *r1 = high_bits_32(r);

  *r0 = (int32_t)r;
  *r0 -= *r1 * 2 * ((K_PRIME - 1) / 32);
  *r0 -= (((int32_t)K_HALF_PRIME - *r0) >> 31) & (int32_t)K_PRIME;
}

// FIPS 204, Algorithm 36 (`Decompose`), specialized to γ2 = (q - 1)/88.
static void decompose_88(uint32_t *r1, int32_t *r0, uint32_t r) {
  *r1 = high_bits_88(r);

  *r0 = (int32_t)r;
  *r0 -= *r1 * 2 * ((K_PRIME - 1) / 88);
  *r0 -= (((int32_t)K_HALF_PRIME - *r0) >> 31) & (int32_t)K_PRIME;
}

// FIPS 204, Algorithm 38 (`LowBits`), specialized to γ2 = (q - 1)/32.
static int32_t low_bits_32(uint32_t x) {
  uint32_t r1;
  int32_t r0;
  decompose_32(&r1, &r0, x);
  return r0;
}

// FIPS 204, Algorithm 38 (`LowBits`), specialized to γ2 = (q - 1)/88.
static int32_t low_bits_88(uint32_t x) {
  uint32_t r1;
  int32_t r0;
  decompose_88(&r1, &r0, x);
  return r0;
}

// FIPS 204, Algorithm 39 (`MakeHint`), specialized to γ2 = (q - 1)/32.
//
// In the spec this takes two arguments, z and r, and is called with
//   z = -ct0
//   r = w - cs2 + ct0
//
// It then computes HighBits (algorithm 37) of z and z+r. But z+r is just w -
// cs2, so this takes three arguments and saves an addition.
static uint32_t make_hint_32(uint32_t ct0, uint32_t cs2, uint32_t w) {
  uint32_t r_plus_z = mod_sub(w, cs2);
  uint32_t r = reduce_once(r_plus_z + ct0);
  return high_bits_32(r) != high_bits_32(r_plus_z);
}

// FIPS 204, Algorithm 39 (`MakeHint`), specialized to γ2 = (q - 1)/88.
static uint32_t make_hint_88(uint32_t ct0, uint32_t cs2, uint32_t w) {
  uint32_t r_plus_z = mod_sub(w, cs2);
  uint32_t r = reduce_once(r_plus_z + ct0);
  return high_bits_88(r) != high_bits_88(r_plus_z);
}

static uint32_t use_hint_32(uint32_t h, uint32_t r) {
  uint32_t r1;
  int32_t r0;
  decompose_32(&r1, &r0, r);

  if (h) {
    if (r0 > 0) {
      // m = 16, thus |mod m| in the spec turns into |& 15|.
      return (r1 + 1) & 15;
    } else {
      return (r1 - 1) & 15;
    }
  }
  return r1;
}

static uint32_t use_hint_88(uint32_t h, uint32_t r) {
  uint32_t r1;
  int32_t r0;
  decompose_88(&r1, &r0, r);

  if (h) {
    // m = 44
    if (r0 > 0) {
      if (r1 == 43) {
        return 0;
      } else {
        return r1 + 1;
      }
    } else {
      if (r1 == 0) {
        return 43;
      } else {
        return r1 - 1;
      }
    }
  }
  return r1;
}

void scalar_high_bits_32(scalar_t *out, const scalar_t *in) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = high_bits_32(in->c[i]);
  }
}

void scalar_high_bits_88(scalar_t *out, const scalar_t *in) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = high_bits_88(in->c[i]);
  }
}

void scalar_low_bits_32(scalar_t *out, const scalar_t *in) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = (uint32_t)low_bits_32(in->c[i]);
  }
}

void scalar_low_bits_88(scalar_t *out, const scalar_t *in) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = (uint32_t)low_bits_88(in->c[i]);
  }
}

void scalar_make_hint_32(scalar_t *out, const scalar_t *ct0,
                         const scalar_t *cs2, const scalar_t *w) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = make_hint_32(ct0->c[i], cs2->c[i], w->c[i]);
  }
}

void scalar_make_hint_88(scalar_t *out, const scalar_t *ct0,
                         const scalar_t *cs2, const scalar_t *w) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    out->c[i] = make_hint_88(ct0->c[i], cs2->c[i], w->c[i]);
  }
}

// FIPS 204, Algorithm 40 (`UseHint`), specialized to γ2 = (q - 1)/32.
// Note: `num_hints` is assumed to be less than or equal to the length of
// `h_bytes`.
void scalar_use_hint_32(scalar_t *out, const uint8_t *h_bytes,
                        uint8_t num_hints, const scalar_t *r) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    int in_list = 0;
    for (size_t j = 0; j < num_hints; j++) {
      if (h_bytes[j] == i) {
        in_list = 1;
        break;
      }
    }
    if (in_list) {
      out->c[i] = use_hint_32(1, r->c[i]);
    } else {
      out->c[i] = use_hint_32(0, r->c[i]);
    }
  }
}

// FIPS 204, Algorithm 40 (`UseHint`), specialized to γ2 = (q - 1)/88.
// Note: `num_hints` is assumed to be less than or equal to the length of
// `h_bytes`.
void scalar_use_hint_88(scalar_t *out, const uint8_t *h_bytes,
                        uint8_t num_hints, const scalar_t *r) {
  for (size_t i = 0; i < K_DEGREE; i++) {
    int in_list = 0;
    for (size_t j = 0; j < num_hints; j++) {
      if (h_bytes[j] == i) {
        in_list = 1;
        break;
      }
    }
    if (in_list) {
      out->c[i] = use_hint_88(1, r->c[i]);
    } else {
      out->c[i] = use_hint_88(0, r->c[i]);
    }
  }
}

/* Bit packing. */

// FIPS 204, Algorithm 16 (`SimpleBitPack`). Specialized to bitlen(b) = 4.
void scalar_encode_4(uint8_t out[128], const scalar_t *s) {
  for (size_t i = 0; i < K_DEGREE / 2; i++) {
    uint32_t a = s->c[2 * i];
    uint32_t b = s->c[2 * i + 1];
    out[i] = (uint8_t)(a | (b << 4));
  }
}

// FIPS 204, Algorithm 16 (`SimpleBitPack`). Specialized to bitlen(b) = 6.
void scalar_encode_6(uint8_t out[192], const scalar_t *s) {
  for (int i = 0; i < K_DEGREE / 4; i++) {
    uint32_t a = s->c[4 * i];
    uint32_t b = s->c[4 * i + 1];
    uint32_t c = s->c[4 * i + 2];
    uint32_t d = s->c[4 * i + 3];
    out[3 * i] = (uint8_t)(a | (b << 6));
    out[3 * i + 1] = (uint8_t)((b >> 2) | (c << 4));
    out[3 * i + 2] = (uint8_t)((c >> 4) | (d << 2));
  }
}

// FIPS 204, Algorithm 16 (`SimpleBitPack`). Specialized to bitlen(b) = 10.
void scalar_encode_10(uint8_t out[320], const scalar_t *s) {
  for (size_t i = 0; i < K_DEGREE / 4; i++) {
    uint32_t a = s->c[4 * i];
    uint32_t b = s->c[4 * i + 1];
    uint32_t c = s->c[4 * i + 2];
    uint32_t d = s->c[4 * i + 3];
    out[5 * i] = (uint8_t)a;
    out[5 * i + 1] = (uint8_t)((a >> 8) | (b << 2));
    out[5 * i + 2] = (uint8_t)((b >> 6) | (c << 4));
    out[5 * i + 3] = (uint8_t)((c >> 4) | (d << 6));
    out[5 * i + 4] = (uint8_t)(d >> 2);
  }
}

// FIPS 204, Algorithm 17 (`BitPack`). Specialized to bitlen(a+b) = 18 and b =
// 2^17.
void scalar_encode_signed_18_17(uint8_t out[576], const scalar_t *s) {
  static const uint32_t kMax = 1u << 17;
  for (int i = 0; i < K_DEGREE / 4; i++) {
    uint32_t a = mod_sub(kMax, s->c[4 * i]);
    uint32_t b = mod_sub(kMax, s->c[4 * i + 1]);
    uint32_t c = mod_sub(kMax, s->c[4 * i + 2]);
    uint32_t d = mod_sub(kMax, s->c[4 * i + 3]);
    out[9 * i] = (uint8_t)a;
    out[9 * i + 1] = (uint8_t)(a >> 8);
    out[9 * i + 2] = (uint8_t)(a >> 16) | (uint8_t)(b << 2);
    out[9 * i + 3] = (uint8_t)(b >> 6);
    out[9 * i + 4] = (uint8_t)(b >> 14) | (uint8_t)(c << 4);
    out[9 * i + 5] = (uint8_t)(c >> 4);
    out[9 * i + 6] = (uint8_t)(c >> 12) | (uint8_t)(d << 6);
    out[9 * i + 7] = (uint8_t)(d >> 2);
    out[9 * i + 8] = (uint8_t)(d >> 10);
  }
}

// FIPS 204, Algorithm 17 (`BitPack`). Specialized to bitlen(a+b) = 20 and b =
// 2^19.
void scalar_encode_signed_20_19(uint8_t out[640], const scalar_t *s) {
  const uint32_t kMax = 1u << 19;
  for (size_t i = 0; i < K_DEGREE / 4; i++) {
    uint32_t a = mod_sub(kMax, s->c[4 * i]);
    uint32_t b = mod_sub(kMax, s->c[4 * i + 1]);
    uint32_t c = mod_sub(kMax, s->c[4 * i + 2]);
    uint32_t d = mod_sub(kMax, s->c[4 * i + 3]);
    a |= b << 20;
    b >>= 12;
    b |= c << 8;
    b |= d << 28;
    d >>= 4;
    memcpy(&out[10 * i], &a, sizeof(a));
    memcpy(&out[10 * i + 4], &b, sizeof(b));
    memcpy(&out[10 * i + 8], &d, 2);
  }
}

// FIPS 204, Algorithm 18 (`SimpleBitUnpack`). Specialized for bitlen(b) == 10.
void scalar_decode_10(scalar_t *out, const uint8_t in[320]) {
  uint32_t v;
  for (size_t i = 0; i < K_DEGREE / 4; i++) {
    memcpy(&v, &in[5 * i], sizeof(v));
    out->c[4 * i] = v & 0x3FF;
    out->c[4 * i + 1] = (v >> 10) & 0x3FF;
    out->c[4 * i + 2] = (v >> 20) & 0x3FF;
    out->c[4 * i + 3] = (v >> 30) | (((uint32_t)in[5 * i + 4]) << 2);
  }
}

// FIPS 204, Algorithm 19 (`BitUnpack`). Specialized to bitlen(a+b) = 18 and b =
// 2^17.
void scalar_decode_signed_18_17(scalar_t *out, const uint8_t in[576]) {
  static const uint32_t kMax = 1u << 17;

  for (int i = 0; i < K_DEGREE / 4; i++) {
    uint32_t a = (uint32_t)in[9 * i] | ((uint32_t)in[9 * i + 1] << 8) |
                 (((uint32_t)in[9 * i + 2] & 0x3) << 16);
    uint32_t b = ((uint32_t)in[9 * i + 2] >> 2) |
                 ((uint32_t)in[9 * i + 3] << 6) |
                 (((uint32_t)in[9 * i + 4] & 0xf) << 14);
    uint32_t c = ((uint32_t)in[9 * i + 4] >> 4) |
                 ((uint32_t)in[9 * i + 5] << 4) |
                 (((uint32_t)in[9 * i + 6] & 0x3f) << 12);
    uint32_t d = ((uint32_t)in[9 * i + 6] >> 6) |
                 ((uint32_t)in[9 * i + 7] << 2) |
                 ((uint32_t)in[9 * i + 8] << 10);

    out->c[i * 4] = mod_sub(kMax, a);
    out->c[i * 4 + 1] = mod_sub(kMax, b);
    out->c[i * 4 + 2] = mod_sub(kMax, c);
    out->c[i * 4 + 3] = mod_sub(kMax, d);
  }
}

// FIPS 204, Algorithm 19 (`BitUnpack`). Specialized to bitlen(a+b) = 20 and b =
// 2^19.
void scalar_decode_signed_20_19(scalar_t *out, const uint8_t in[640]) {
  const uint32_t kMax = 1u << 19;
  const uint32_t k20Bits = (1u << 20) - 1;

  uint32_t a, b;
  uint16_t c;
  for (size_t i = 0; i < K_DEGREE / 4; i++) {
    memcpy(&a, &in[10 * i], sizeof(a));
    memcpy(&b, &in[10 * i + 4], sizeof(b));
    memcpy(&c, &in[10 * i + 8], sizeof(c));

    // It's not possible for a 20-bit number to be out of range when the max is
    // 2^19.
    out->c[i * 4] = mod_sub(kMax, a & k20Bits);
    out->c[i * 4 + 1] = mod_sub(kMax, (a >> 20) | ((b & 0xFF) << 12));
    out->c[i * 4 + 2] = mod_sub(kMax, (b >> 8) & k20Bits);
    out->c[i * 4 + 3] = mod_sub(kMax, (b >> 28) | ((uint32_t)c) << 4);
  }
}

/* Expansion functions. */

// FIPS 204, Algorithm 29 (`SampleInBall`).
void scalar_sample_in_ball_vartime(size_t tau, scalar_t *out,
                                   const uint8_t *seed, size_t len) {
  shake256_ctxt_t shake256_ctxt;
  SHAKE256_init(&shake256_ctxt);
  SHAKE256_absorb(&shake256_ctxt, seed, len);

  uint8_t block[136];
  SHAKE256_squeeze(&shake256_ctxt, block, sizeof(block));

  uint64_t signs;
  memcpy(&signs, block, sizeof(signs));
  int offset = 8;

  // SampleInBall implements a Fisher–Yates shuffle, which unavoidably leaks
  // where the zeros are by memory access pattern. Although this leak happens
  // before bad signatures are rejected, this is safe. See
  // https://boringssl-review.googlesource.com/c/boringssl/+/67747/comment/8d8f01ac_70af3f21/

  memset(out, 0, sizeof(*out));
  for (size_t i = K_DEGREE - tau; i < K_DEGREE; i++) {
    size_t byte;
    for (;;) {
      if (offset == 136) {
        SHAKE256_squeeze(&shake256_ctxt, block, sizeof(block));
        offset = 0;
      }

      byte = block[offset++];
      if (byte <= i) {
        break;
      }
    }

    out->c[i] = out->c[byte];
    out->c[byte] = mod_sub(1, 2 * (signs & 1));
    signs >>= 1;
  }

  SHAKE256_free(&shake256_ctxt);
}

// FIPS 204, Algorithm 30 (`RejNTTPoly`).
//
// Rejection samples a Keccak stream to get uniformly distributed elements. This
// is used for matrix expansion and only operates on public inputs.
void scalar_from_keccak_vartime(scalar_t *out,
                                const uint8_t derived_seed[K_RHO_BYTES + 2]) {
  shake128_ctxt_t shake128_ctxt;
  SHAKE128_init(&shake128_ctxt);
  SHAKE128_absorb(&shake128_ctxt, derived_seed, K_RHO_BYTES + 2);

  int done = 0;
  while (done < K_DEGREE) {
    uint8_t block[168];
    SHAKE128_squeeze(&shake128_ctxt, block, sizeof(block));
    for (size_t i = 0; i < sizeof(block) && done < K_DEGREE; i += 3) {
      // FIPS 204, Algorithm 14 (`CoeffFromThreeBytes`).
      uint32_t value = (uint32_t)block[i] | ((uint32_t)block[i + 1] << 8) |
                       (((uint32_t)block[i + 2] & 0x7F) << 16);
      if (value < K_PRIME) {
        out->c[done++] = value;
      }
    }
  }

  SHAKE128_free(&shake128_ctxt);
}

static int coefficient_from_nibble_2(uint32_t nibble, uint32_t *result) {
  if (nibble < 15) {
    // Constant time "nibble % 5".
    nibble = nibble - 5 * ((205 * nibble) >> 10);
    *result = mod_sub(2, nibble);
    return 1;
  }
  return 0;
}

static int coefficient_from_nibble_4(uint32_t nibble, uint32_t *result) {
  if (nibble < 9) {
    *result = mod_sub(4, nibble);
    return 1;
  }
  return 0;
}

// FIPS 204, Algorithm 31 (`RejBoundedPoly`), specialized to η = 2.
void scalar_uniform_2(scalar_t *out,
                      const uint8_t derived_seed[K_SIGMA_BYTES + 2]) {
  shake256_ctxt_t shake256_ctxt;
  SHAKE256_init(&shake256_ctxt);
  SHAKE256_absorb(&shake256_ctxt, derived_seed, K_SIGMA_BYTES + 2);

  int done = 0;
  while (done < K_DEGREE) {
    uint8_t block[136];
    SHAKE256_squeeze(&shake256_ctxt, block, sizeof(block));
    for (size_t i = 0; i < sizeof(block) && done < K_DEGREE; ++i) {
      uint32_t t0 = block[i] & 0x0F;
      uint32_t t1 = block[i] >> 4;
      // FIPS 204, Algorithm 15 (`CoefFromHalfByte`). Although both the input
      // and output here are secret, it is OK to leak when we rejected a byte.
      // Individual bytes of the SHAKE-256 stream are (indistinguishable from)
      // independent of each other and the original seed, so leaking information
      // about the rejected bytes does not reveal the input or output.
      uint32_t v;
      if (coefficient_from_nibble_2(t0, &v)) {
        out->c[done++] = v;
      }
      if (done < K_DEGREE && coefficient_from_nibble_2(t1, &v)) {
        out->c[done++] = v;
      }
    }
  }

  SHAKE256_free(&shake256_ctxt);
}

// FIPS 204, Algorithm 31 (`RejBoundedPoly`), specialized to η = 4.
void scalar_uniform_4(scalar_t *out,
                      const uint8_t derived_seed[K_SIGMA_BYTES + 2]) {
  shake256_ctxt_t shake256_ctxt;
  SHAKE256_init(&shake256_ctxt);
  SHAKE256_absorb(&shake256_ctxt, derived_seed, K_SIGMA_BYTES + 2);

  int done = 0;
  while (done < K_DEGREE) {
    uint8_t block[136];
    SHAKE256_squeeze(&shake256_ctxt, block, sizeof(block));
    for (size_t i = 0; i < sizeof(block) && done < K_DEGREE; ++i) {
      uint32_t t0 = block[i] & 0x0F;
      uint32_t t1 = block[i] >> 4;
      // FIPS 204, Algorithm 15 (`CoefFromHalfByte`). Although both the input
      // and output here are secret, it is OK to leak when we rejected a byte.
      // Individual bytes of the SHAKE-256 stream are (indistinguishable from)
      // independent of each other and the original seed, so leaking information
      // about the rejected bytes does not reveal the input or output.
      uint32_t v;
      if (coefficient_from_nibble_4(t0, &v)) {
        out->c[done++] = v;
      }
      if (done < K_DEGREE && coefficient_from_nibble_4(t1, &v)) {
        out->c[done++] = v;
      }
    }
  }

  SHAKE256_free(&shake256_ctxt);
}

// FIPS 204, Algorithm 33 (`ExpandS`), specialized to η = 2.
void expand_scalar_2(scalar_t *out, const uint8_t sigma[K_SIGMA_BYTES],
                     size_t i) {
  uint8_t derived_seed[K_SIGMA_BYTES + 2];
  memcpy(derived_seed, sigma, K_SIGMA_BYTES);
  derived_seed[K_SIGMA_BYTES] = (uint8_t)i;
  derived_seed[K_SIGMA_BYTES + 1] = 0;
  scalar_uniform_2(out, derived_seed);
}

// FIPS 204, Algorithm 33 (`ExpandS`), specialized to η = 4.
void expand_scalar_4(scalar_t *out, const uint8_t sigma[K_SIGMA_BYTES],
                     size_t i) {
  uint8_t derived_seed[K_SIGMA_BYTES + 2];
  memcpy(derived_seed, sigma, K_SIGMA_BYTES);
  derived_seed[K_SIGMA_BYTES] = (uint8_t)i;
  derived_seed[K_SIGMA_BYTES + 1] = 0;
  scalar_uniform_4(out, derived_seed);
}

// FIPS 204, Algorithm 34 (`ExpandMask`), but just a single step.
// Specialized to γ1 = 17.
static void scalar_sample_mask_17(
    scalar_t *out, const uint8_t derived_seed[K_RHO_PRIME_BYTES + 2]) {
  uint8_t buf[576];
  SHAKE256_buffer(buf, sizeof(buf), derived_seed, K_RHO_PRIME_BYTES + 2);

  scalar_decode_signed_18_17(out, buf);
}

// FIPS 204, Algorithm 34 (`ExpandMask`) for a single scalar.
// Specialized to γ1 = 17.
void scalar_expand_mask_17(scalar_t *out, const uint8_t seed[K_RHO_PRIME_BYTES],
                           size_t kappa, size_t i) {
  uint8_t derived_seed[K_RHO_PRIME_BYTES + 2];
  memcpy(derived_seed, seed, K_RHO_PRIME_BYTES);
  size_t index = kappa + i;
  derived_seed[K_RHO_PRIME_BYTES] = index & 0xFF;
  derived_seed[K_RHO_PRIME_BYTES + 1] = (index >> 8) & 0xFF;
  scalar_sample_mask_17(out, derived_seed);
}

// FIPS 204, Algorithm 34 (`ExpandMask`), but just a single step.
// Specialized to γ1 = 19.
static void scalar_sample_mask_19(
    scalar_t *out, const uint8_t derived_seed[K_RHO_PRIME_BYTES + 2]) {
  uint8_t buf[640];
  SHAKE256_buffer(buf, sizeof(buf), derived_seed, K_RHO_PRIME_BYTES + 2);

  scalar_decode_signed_20_19(out, buf);
}

// FIPS 204, Algorithm 34 (`ExpandMask`).
// Specialized to γ1 = 19.
void scalar_expand_mask_19(scalar_t *out, const uint8_t seed[K_RHO_PRIME_BYTES],
                           size_t kappa, size_t i) {
  uint8_t derived_seed[K_RHO_PRIME_BYTES + 2];
  memcpy(derived_seed, seed, K_RHO_PRIME_BYTES);
  size_t index = kappa + i;
  derived_seed[K_RHO_PRIME_BYTES] = index & 0xFF;
  derived_seed[K_RHO_PRIME_BYTES + 1] = (index >> 8) & 0xFF;
  scalar_sample_mask_19(out, derived_seed);
}
