// Copyright 2024 The BoringSSL Authors
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

#ifndef OPENTITAN_THIRD_PARTY_EMBEDPQC_MLDSA44_TINY_H_
#define OPENTITAN_THIRD_PARTY_EMBEDPQC_MLDSA44_TINY_H_

#include <stddef.h>
#include <stdint.h>

#include "third_party/embedpqc/mldsa_mu.h"

#ifdef __cplusplus
extern "C" {
#endif

#ifndef MLDSA44_PRIVATE_SEED_BYTES
#define MLDSA44_PRIVATE_SEED_BYTES 32
#endif
#ifndef MLDSA44_RANDOMIZER_BYTES
#define MLDSA44_RANDOMIZER_BYTES 32
#endif
#ifndef MLDSA44_PUBLIC_KEY_BYTES
#define MLDSA44_PUBLIC_KEY_BYTES 1312
#endif
#ifndef MLDSA44_SIGNATURE_BYTES
#define MLDSA44_SIGNATURE_BYTES 2420
#endif

void mldsa44_tiny_pub_from_seed(
    uint8_t out_encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES]);

void mldsa44_tiny_sign(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES],
    const uint8_t randomizer[MLDSA44_RANDOMIZER_BYTES], const uint8_t *msg,
    size_t msg_len);

void mldsa44_tiny_sign_mu(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES],
    const uint8_t randomizer[MLDSA44_RANDOMIZER_BYTES],
    const uint8_t mu[K_MU_BYTES]);

void mldsa44_tiny_sign_deterministic(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES],
    const uint8_t *msg, size_t msg_len);

void mldsa44_tiny_sign_mu_deterministic(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES],
    const uint8_t mu[K_MU_BYTES]);

int mldsa44_tiny_verify(
    const uint8_t encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES],
    const uint8_t encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t *msg, size_t msg_len);

int mldsa44_tiny_verify_mu(
    const uint8_t encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES],
    const uint8_t encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t mu[K_MU_BYTES]);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_THIRD_PARTY_EMBEDPQC_MLDSA44_TINY_H_
