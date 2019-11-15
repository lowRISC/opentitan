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
#ifndef SECURITY_UTIL_LITE_P256_PRNG_H_
#define SECURITY_UTIL_LITE_P256_PRNG_H_

// Pseudo-random generator.
// Inspired by NIST SP 800-90A HMAC_DRBG.
//
// Each call to p256_prng_draw() yields 256 pseudo random bits.
// The output can be used for emphemeral DH handshakes and other
// cryptographic operations.
//
// NOTE: leakage of initial- and subsequent (if any) seed material allows for
// re-generation of the psuedo random sequence and thus derived key material.

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

#define P256_PRNG_SIZE 32

typedef struct P256_PRNG_CTX {
  uint32_t Key[P256_PRNG_SIZE];
  uint32_t V[P256_PRNG_SIZE];
  uint64_t instance_count;
  uint64_t call_count;
} P256_PRNG_CTX;

// Initialize the pool with entropy.
// instance_count should increase over the life of the seed.
// For an embedded system with fixed seed, a persistent hard boot
// counter would be good choice.
void p256_prng_init(P256_PRNG_CTX* ctx,
                    const void* seed, size_t seed_size,
                    uint64_t instance_count);

// Return 256 bits of pseudo-random from the pool.
void p256_prng_draw(P256_PRNG_CTX* ctx,
                    uint8_t dst[P256_PRNG_SIZE]);

// Mix additional entropy into prng instance.
void p256_prng_add(P256_PRNG_CTX* ctx,
                   const void* seed, size_t seed_size);

#ifdef __cplusplus
}
#endif

#endif  // SECURITY_UTIL_LITE_P256_PRNG_H_
