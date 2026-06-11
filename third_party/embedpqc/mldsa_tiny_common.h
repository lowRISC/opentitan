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

#ifndef OPENTITAN_THIRD_PARTY_EMBEDPQC_MLDSA_TINY_COMMON_H_
#define OPENTITAN_THIRD_PARTY_EMBEDPQC_MLDSA_TINY_COMMON_H_

#include <stddef.h>
#include <stdint.h>

/* Arithmetic parameters. */

// 2^23 - 2^13 + 1
#define K_PRIME 8380417
// Inverse of -K_PRIME modulo 2^32
#define K_PRIME_NEG_INVERSE 4236238847
#define K_DROPPED_BITS 13
#define K_HALF_PRIME ((K_PRIME - 1) / 2)
#define K_DEGREE 256
// 256^-1 mod K_PRIME, in Montgomery form.
#define K_INVERSE_DEGREE_MONTGOMERY 41978

/* Common sizes. */

#define K_RHO_BYTES 32
#define K_SIGMA_BYTES 64
#define K_K_BYTES 32
#define K_RHO_PRIME_BYTES 64

/* Fundamental types. */

typedef struct {
  uint32_t c[K_DEGREE];
} scalar_t;

/* Arithmetic. */

// Reduces x mod K_PRIME in constant time, where 0 <= x < 2*K_PRIME.
uint32_t reduce_once(uint32_t x);

uint32_t mod_sub(uint32_t a, uint32_t b);

void scalar_add(scalar_t *out, const scalar_t *lhs, const scalar_t *rhs);

void scalar_sub(scalar_t *out, const scalar_t *lhs, const scalar_t *rhs);

// Multiply two scalars in NTT form.
void scalar_mul(scalar_t *out, const scalar_t *lhs, const scalar_t *rhs);

// For scalars a, b, c in NTT form, compute a + b * c.
void scalar_mul_add(scalar_t *out, const scalar_t *a, const scalar_t *b,
                    const scalar_t *c);

// In place number theoretic transform of a given scalar.
//
// FIPS 204, Algorithm 41 (`NTT`).
void scalar_ntt(scalar_t *s);

// In place inverse number theoretic transform of a given scalar.
//
// FIPS 204, Algorithm 42 (`NTT^-1`).
void scalar_inverse_ntt(scalar_t *s);

/* Rounding and hints. */

// The input vector contains only zeroes and ones.
size_t scalar_count_ones(const scalar_t *s);

// FIPS 204, Algorithm 35 (`Power2Round`).
void power2_round(uint32_t *r1, uint32_t *r0, uint32_t r);

// Scale back previously rounded value.
void scale_power2_round(uint32_t *out, uint32_t r1);

void scalar_power2_round(scalar_t *s1, scalar_t *s0, const scalar_t *s);

void scalar_scale_power2_round(scalar_t *out, const scalar_t *in);

void scalar_max(uint32_t *max, const scalar_t *s);

void scalar_max_signed(uint32_t *max, const scalar_t *s);

void scalar_high_bits_32(scalar_t *out, const scalar_t *in);

void scalar_high_bits_88(scalar_t *out, const scalar_t *in);

void scalar_low_bits_32(scalar_t *out, const scalar_t *in);

void scalar_low_bits_88(scalar_t *out, const scalar_t *in);

void scalar_make_hint_32(scalar_t *out, const scalar_t *ct0,
                         const scalar_t *cs2, const scalar_t *w);

void scalar_make_hint_88(scalar_t *out, const scalar_t *ct0,
                         const scalar_t *cs2, const scalar_t *w);

// FIPS 204, Algorithm 40 (`UseHint`), specialized to γ2 = (q - 1)/32.
void scalar_use_hint_32(scalar_t *out, const uint8_t *h_bytes,
                        uint8_t num_hints, const scalar_t *r);

// FIPS 204, Algorithm 40 (`UseHint`), specialized to γ2 = (q - 1)/88.
void scalar_use_hint_88(scalar_t *out, const uint8_t *h_bytes,
                        uint8_t num_hints, const scalar_t *r);

/* Bit packing. */

// FIPS 204, Algorithm 16 (`SimpleBitPack`). Specialized to bitlen(b) = 4.
void scalar_encode_4(uint8_t out[128], const scalar_t *s);

// FIPS 204, Algorithm 16 (`SimpleBitPack`). Specialized to bitlen(b) = 6.
void scalar_encode_6(uint8_t out[192], const scalar_t *s);

// FIPS 204, Algorithm 16 (`SimpleBitPack`). Specialized to bitlen(b) = 10.
void scalar_encode_10(uint8_t out[320], const scalar_t *s);

// FIPS 204, Algorithm 17 (`BitPack`). Specialized to bitlen(a+b) = 18 and b =
// 2^17.
void scalar_encode_signed_18_17(uint8_t out[576], const scalar_t *s);

// FIPS 204, Algorithm 17 (`BitPack`). Specialized to bitlen(a+b) = 20 and b =
// 2^19.
void scalar_encode_signed_20_19(uint8_t out[640], const scalar_t *s);

// FIPS 204, Algorithm 18 (`SimpleBitUnpack`). Specialized for bitlen(b)
// == 10.
void scalar_decode_10(scalar_t *out, const uint8_t in[320]);

// FIPS 204, Algorithm 19 (`BitUnpack`). Specialized to bitlen(a+b) = 18 and b =
// 2^17.
void scalar_decode_signed_18_17(scalar_t *out, const uint8_t in[576]);

// FIPS 204, Algorithm 19 (`BitUnpack`). Specialized to bitlen(a+b) = 20 and b =
// 2^19.
void scalar_decode_signed_20_19(scalar_t *out, const uint8_t in[640]);

/* Expansion functions. */

// FIPS 204, Algorithm 29 (`SampleInBall`).
void scalar_sample_in_ball_vartime(size_t tau, scalar_t *out,
                                   const uint8_t *seed, size_t len);

// FIPS 204, Algorithm 30 (`RejNTTPoly`).
//
// Rejection samples a Keccak stream to get uniformly distributed elements.
// This is used for matrix expansion and only operates on public inputs.
void scalar_from_keccak_vartime(scalar_t *out,
                                const uint8_t derived_seed[K_RHO_BYTES + 2]);

// FIPS 204, Algorithm 31 (`RejBoundedPoly`), specialized to η = 2.
void scalar_uniform_2(scalar_t *out,
                      const uint8_t derived_seed[K_SIGMA_BYTES + 2]);

// FIPS 204, Algorithm 31 (`RejBoundedPoly`), specialized to η = 4.
void scalar_uniform_4(scalar_t *out,
                      const uint8_t derived_seed[K_SIGMA_BYTES + 2]);

// FIPS 204, Algorithm 33 (`ExpandS`), specialized to η = 2.
void expand_scalar_2(scalar_t *out, const uint8_t sigma[K_SIGMA_BYTES],
                     size_t i);

// FIPS 204, Algorithm 33 (`ExpandS`), specialized to η = 4.
void expand_scalar_4(scalar_t *out, const uint8_t sigma[K_SIGMA_BYTES],
                     size_t i);

// FIPS 204, Algorithm 34 (`ExpandMask`), specialized to γ1 = 17.
void scalar_expand_mask_17(scalar_t *out, const uint8_t seed[K_RHO_PRIME_BYTES],
                           size_t kappa, size_t i);

// FIPS 204, Algorithm 34 (`ExpandMask`), specialized to γ1 = 19.
void scalar_expand_mask_19(scalar_t *out, const uint8_t seed[K_RHO_PRIME_BYTES],
                           size_t kappa, size_t i);

#endif  // OPENTITAN_THIRD_PARTY_EMBEDPQC_MLDSA_TINY_COMMON_H_
