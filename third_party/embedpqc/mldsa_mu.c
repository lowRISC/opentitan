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

#include "third_party/embedpqc/mldsa_mu.h"

#include <stddef.h>
#include <stdint.h>

#include "third_party/embedpqc/shake.h"

// Computes the mu value for a given public key, context, and message.
// µ is the "message representative that may optionally be computed in a
// different cryptographic module" as referenced in Algorithm 7, line 6.
void compute_mu(uint8_t out_mu[K_MU_BYTES], const uint8_t *encoded_public_key,
                size_t encoded_public_key_len, const uint8_t *context,
                uint8_t context_len, const uint8_t *msg, size_t msg_len) {
  // Re-use out_mu to store the public key hash first.
  SHAKE256_buffer(out_mu, K_MU_BYTES, encoded_public_key,
                  encoded_public_key_len);
  compute_mu_from_public_key_hash(out_mu, out_mu, context, context_len, msg,
                                  msg_len);
}

// As `compute_mu`, except using the `public_key_hash` (`tr` in FIPS 204),
// which is computed as SHAKE256_512(encoded_public_key).
//
// It is safe for `out_mu` and `public_key_hash` to be the same buffer.
void compute_mu_from_public_key_hash(uint8_t out_mu[K_MU_BYTES],
                                     const uint8_t public_key_hash[K_TR_BYTES],
                                     const uint8_t *context,
                                     uint8_t context_len, const uint8_t *msg,
                                     size_t msg_len) {
  shake256_ctxt_t shake256_ctxt;
  SHAKE256_init(&shake256_ctxt);
  SHAKE256_absorb(&shake256_ctxt, public_key_hash, K_TR_BYTES);
  uint8_t context_prefix[2] = {0, context_len};
  SHAKE256_absorb(&shake256_ctxt, context_prefix, 2);
  SHAKE256_absorb(&shake256_ctxt, context, context_len);
  SHAKE256_absorb(&shake256_ctxt, msg, msg_len);
  SHAKE256_squeeze(&shake256_ctxt, out_mu, K_MU_BYTES);
  SHAKE256_free(&shake256_ctxt);
}
