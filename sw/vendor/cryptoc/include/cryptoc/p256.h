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
#ifndef SECURITY_UTIL_LITE_P256_H_
#define SECURITY_UTIL_LITE_P256_H_

// Collection of routines manipulating 256 bit unsigned integers.
// Just enough to implement ecdsa-p256 and related algorithms.
//
// To determine suitability of this code for your target platform
// and compiler combination, make sure p256_unittest succeeds.

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define P256_BITSPERDIGIT 32
#define P256_NDIGITS 8
#define P256_NBYTES 32

typedef int p256_err;
typedef uint32_t p256_digit;
typedef int32_t p256_sdigit;
typedef uint64_t p256_ddigit;
typedef int64_t p256_sddigit;

// Defining p256_int as struct to leverage struct assigment.
typedef struct
#ifdef SUPPORT_UNALIGNED
               __attribute__((packed))
#endif
{
  p256_digit a[P256_NDIGITS];
} p256_int;

extern const p256_int SECP256r1_n;  // Curve order
extern const p256_int SECP256r1_nMin2;  // Curve order - 2
extern const p256_int SECP256r1_p;  // Curve prime
extern const p256_int SECP256r1_b;  // Curve param

// Initialize a p256_int to zero.
void p256_init(p256_int* a);

// Clear a p256_int to zero.
void p256_clear(p256_int* a);

// Return bit. Index 0 is least significant.
int p256_get_bit(const p256_int* a, int index);

// b := a % MOD
void p256_mod(
    const p256_int* MOD,
    const p256_int* a,
    p256_int* b);

// c := a * (top_b | b) % MOD
void p256_modmul(
    const p256_int* MOD,
    const p256_int* a,
    const p256_digit top_b,
    const p256_int* b,
    p256_int* c);

// b := 1 / a % MOD
// MOD best be SECP256r1_n
void p256_modinv(
    const p256_int* MOD,
    const p256_int* a,
    p256_int* b);

// b := 1 / a % MOD
// MOD best be SECP256r1_n
// Faster than p256_modinv()
void p256_modinv_vartime(
    const p256_int* MOD,
    const p256_int* a,
    p256_int* b);

// b := a << (n % P256_BITSPERDIGIT)
// Returns the bits shifted out of most significant digit.
p256_digit p256_shl(const p256_int* a, int n, p256_int* b);

// b := a >> (n % P256_BITSPERDIGIT)
void p256_shr(const p256_int* a, int n, p256_int* b);

int p256_is_zero(const p256_int* a);
int p256_is_odd(const p256_int* a);
int p256_is_even(const p256_int* a);

// Returns -1, 0 or 1.
int p256_cmp(const p256_int* a, const p256_int *b);

// c: = a - b
// Returns -1 on borrow.
int p256_sub(const p256_int* a, const p256_int* b, p256_int* c);

// c := a + b
// Returns 1 on carry.
int p256_add(const p256_int* a, const p256_int* b, p256_int* c);

// c := a + (single digit)b
// Returns carry 1 on carry.
int p256_add_d(const p256_int* a, p256_digit b, p256_int* c);

// ec routines.

// {out_x,out_y} := nG
void p256_base_point_mul(const p256_int *n,
                         p256_int *out_x,
                         p256_int *out_y);

// {out_x,out_y} := n{in_x,in_y}
void p256_point_mul(const p256_int *n,
                    const p256_int *in_x,
                    const p256_int *in_y,
                    p256_int *out_x,
                    p256_int *out_y);

// {out_x,out_y} := n1G + n2{in_x,in_y}
void p256_points_mul_vartime(
    const p256_int *n1, const p256_int *n2,
    const p256_int *in_x, const p256_int *in_y,
    p256_int *out_x, p256_int *out_y);

// Return whether point {x,y} is on curve.
int p256_is_valid_point(const p256_int* x, const p256_int* y);

// Outputs big-endian binary form. No leading zero skips.
void p256_to_bin(const p256_int* src, uint8_t dst[P256_NBYTES]);

// Reads from big-endian binary form,
// thus pre-pad with leading zeros if short.
void p256_from_bin(const uint8_t src[P256_NBYTES], p256_int* dst);

#define P256_DIGITS(x) ((x)->a)
#define P256_DIGIT(x,y) ((x)->a[y])

#define P256_ZERO {{0}}
#define P256_ONE {{1}}

#ifdef __cplusplus
}
#endif

#endif  // SECURITY_UTIL_LITE_P256_H_
