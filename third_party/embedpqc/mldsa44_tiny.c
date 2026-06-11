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

#include "third_party/embedpqc/mldsa44_tiny.h"

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "third_party/embedpqc/ct.h"
#include "third_party/embedpqc/mldsa_mu.h"
#include "third_party/embedpqc/mldsa_tiny_common.h"
#include "third_party/embedpqc/shake.h"

/* ML-DSA-44 parameters. */

#define TAU 39
#define LAMBDA_BYTES (128 / 8)
#define GAMMA1 (1 << 17)
#define K_GAMMA_2 ((K_PRIME - 1) / 88)
#define BETA 78
#define OMEGA 80

/* Fundamental types. */

typedef struct {
  scalar_t v[4];
} vector4_t;

typedef struct {
  uint8_t v[OMEGA];
  uint8_t num_hints;
} hint_ent_t;

typedef struct {
  hint_ent_t v[4];
} hint_t;

/* Complex types. */

typedef struct {
  uint8_t rho[K_RHO_BYTES];
  uint8_t k[K_K_BYTES];
  uint8_t sigma[K_SIGMA_BYTES];
  vector4_t t0_ntt;
} private_key_t;

/* Arithmetic. */

static void vector4_zero(vector4_t *out) { memset(&out->v, 0, sizeof(out->v)); }

static void vector4_add(vector4_t *out, const vector4_t *lhs,
                        const vector4_t *rhs) {
  for (size_t i = 0; i < 4; i++) {
    scalar_add(&out->v[i], &lhs->v[i], &rhs->v[i]);
  }
}

static void vector4_sub(vector4_t *out, const vector4_t *lhs,
                        const vector4_t *rhs) {
  for (size_t i = 0; i < 4; i++) {
    scalar_sub(&out->v[i], &lhs->v[i], &rhs->v[i]);
  }
}

static void vector4_mul_scalar(vector4_t *out, const vector4_t *lhs,
                               const scalar_t *rhs) {
  for (size_t i = 0; i < 4; i++) {
    scalar_mul(&out->v[i], &lhs->v[i], rhs);
  }
}

static void vector4_ntt(vector4_t *a) {
  for (size_t i = 0; i < 4; i++) {
    scalar_ntt(&a->v[i]);
  }
}

static void vector4_inverse_ntt(vector4_t *a) {
  for (size_t i = 0; i < 4; i++) {
    scalar_inverse_ntt(&a->v[i]);
  }
}

/* Rounding and hints. */

static void vector4_power2_round(vector4_t *t1, vector4_t *t0,
                                 const vector4_t *t) {
  for (size_t i = 0; i < 4; i++) {
    scalar_power2_round(&t1->v[i], &t0->v[i], &t->v[i]);
  }
}

static void vector4_scale_power2_round(vector4_t *out, const vector4_t *in) {
  for (size_t i = 0; i < 4; i++) {
    scalar_scale_power2_round(&out->v[i], &in->v[i]);
  }
}

static uint32_t vector4_max(const vector4_t *a) {
  uint32_t max = 0;
  for (size_t i = 0; i < 4; i++) {
    scalar_max(&max, &a->v[i]);
  }
  return max;
}

static void vector4_use_hint(vector4_t *out, const hint_t *h,
                             const vector4_t *r) {
  for (size_t i = 0; i < 4; i++) {
    scalar_use_hint_88(&out->v[i], h->v[i].v, h->v[i].num_hints, &r->v[i]);
  }
}

/* Expansion functions. */

// A combination of FIPS 204, Algorithm 32 (`ExpandA`) and matrix
// multiplication.
static void matrix44_expand_mul(vector4_t *out, const uint8_t rho[K_RHO_BYTES],
                                const vector4_t *a) {
  uint8_t derived_seed[K_RHO_BYTES + 2];
  memcpy(derived_seed, rho, K_RHO_BYTES);
  vector4_zero(out);
  for (size_t i = 0; i < 4; i++) {
    for (size_t j = 0; j < 4; j++) {
      scalar_t m_ij;
      // Step 1: Generate (i,j)-th matrix entry.
      derived_seed[K_RHO_BYTES + 1] = (uint8_t)i;
      derived_seed[K_RHO_BYTES] = (uint8_t)j;
      scalar_from_keccak_vartime(&m_ij, derived_seed);
      // Step 2: Multiply with right hand side and sum into output.
      scalar_mul_add(&out->v[i], &out->v[i], &m_ij, &a->v[j]);
    }
  }
}

static void expand_s1(vector4_t *s1, const uint8_t sigma[K_SIGMA_BYTES]) {
  for (size_t i = 0; i < 4; i++) {
    expand_scalar_2(&s1->v[i], sigma, i);
  }
}

static void expand_s2(vector4_t *s2, const uint8_t sigma[K_SIGMA_BYTES]) {
  for (size_t i = 0; i < 4; i++) {
    expand_scalar_2(&s2->v[i], sigma, i + 4);
  }
}

static void expand_s1_ntt_mul_scalar(scalar_t *out, size_t i,
                                     const uint8_t sigma[K_SIGMA_BYTES],
                                     const scalar_t *rhs) {
  expand_scalar_2(out, sigma, (uint8_t)i);
  scalar_ntt(out);
  scalar_mul(out, out, rhs);
}

static void expand_s2_ntt_mul_scalar(scalar_t *out, size_t i,
                                     const uint8_t sigma[K_SIGMA_BYTES],
                                     const scalar_t *rhs) {
  expand_scalar_2(out, sigma, (uint8_t)i + 4);
  scalar_ntt(out);
  scalar_mul(out, out, rhs);
}

// A combination of FIPS 204, Algorithm 32 (`ExpandA`), matrix
// multiplication, and FIPS 204, Algorithm 34 (`ExpandMask`).
static void matrix44_expand_mul_mask(vector4_t *out,
                                     const uint8_t rho[K_RHO_BYTES],
                                     const uint8_t rho_prime[K_RHO_PRIME_BYTES],
                                     size_t kappa) {
  vector4_zero(out);
  uint8_t derived_seed[K_RHO_BYTES + 2];
  memcpy(derived_seed, rho, K_RHO_BYTES);
  for (size_t j = 0; j < 4; j++) {
    scalar_t y_j;
    scalar_expand_mask_17(&y_j, rho_prime, kappa, j);
    scalar_ntt(&y_j);
    for (size_t i = 0; i < 4; i++) {
      scalar_t m_ij;
      derived_seed[K_RHO_BYTES + 1] = (uint8_t)i;
      derived_seed[K_RHO_BYTES] = (uint8_t)j;
      scalar_from_keccak_vartime(&m_ij, derived_seed);
      scalar_mul_add(&out->v[i], &out->v[i], &m_ij, &y_j);
    }
  }
}

/* Encoding. */

// FIPS 204, Algorithm 16 (`SimpleBitPack`).
static void vector4_encode_10(uint8_t *out, const vector4_t *a) {
  for (size_t i = 0; i < 4; i++) {
    scalar_encode_10(out + i * 10 * K_DEGREE / 8, &a->v[i]);
  }
}

// FIPS 204, Algorithm 18 (`SimpleBitUnpack`).
static void vector4_decode_10(vector4_t *out, const uint8_t *in) {
  for (size_t i = 0; i < 4; i++) {
    scalar_decode_10(&out->v[i], in + i * 10 * K_DEGREE / 8);
  }
}

static void vector4_decode_signed_18_17(vector4_t *out, const uint8_t *in) {
  for (size_t i = 0; i < 4; i++) {
    scalar_decode_signed_18_17(&out->v[i], in + i * 18 * K_DEGREE / 8);
  }
}

// FIPS 204, Algorithm 20 (`HintBitPack`).
static void hint_bit_pack(uint8_t out[OMEGA + 4], const vector4_t *h) {
  memset(out, 0, OMEGA + 4);
  int index = 0;
  for (size_t i = 0; i < 4; i++) {
    for (size_t j = 0; j < K_DEGREE; j++) {
      if (h->v[i].c[j]) {
        // h must have at most OMEGA non-zero coefficients.
        out[index++] = (uint8_t)j;
      }
    }
    out[OMEGA + i] = (uint8_t)index;
  }
}

// FIPS 204, Algorithm 21 (`HintBitUnpack`).
static int hint_bit_unpack(hint_t *h, const uint8_t in[OMEGA + 4]) {
  int index = 0;
  for (size_t i = 0; i < 4; i++) {
    const int limit = in[OMEGA + i];
    if (limit < index || limit > OMEGA) {
      return 0;
    }
    h->v[i].num_hints = 0;
    int last = -1;
    while (index < limit) {
      int byte = in[index++];
      if (last >= 0 && byte <= last) {
        return 0;
      }
      last = byte;
      h->v[i].v[h->v[i].num_hints++] = (uint8_t)byte;
    }
  }
  for (; index < OMEGA; index++) {
    if (in[index] != 0) {
      return 0;
    }
  }
  return 1;
}

// FIPS 204, Algorithm 27 (`sigDecode`).
static int decode_signature(uint8_t c_tilde[2 * LAMBDA_BYTES], vector4_t *z,
                            hint_t *h,
                            const uint8_t in[MLDSA44_SIGNATURE_BYTES]) {
  memcpy(c_tilde, in, 2 * LAMBDA_BYTES);

  const uint8_t *z_input = &in[2 * LAMBDA_BYTES];
  vector4_decode_signed_18_17(z, z_input);

  const uint8_t *hint_input = &in[2 * LAMBDA_BYTES + 576 * 4];
  return hint_bit_unpack(h, hint_input);
}

/* Main algorithms. */

// FIPS 204, Algorithm 6 (`ML-DSA.KeyGen_internal`).
static void generate_key_internal(
    uint8_t out_encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES],
    private_key_t *priv, const uint8_t entropy[MLDSA44_PRIVATE_SEED_BYTES]) {
  uint8_t augmented_entropy[MLDSA44_PRIVATE_SEED_BYTES + 2];
  memcpy(augmented_entropy, entropy, MLDSA44_PRIVATE_SEED_BYTES);
  // The K and L parameters are appended to the seed.
  augmented_entropy[MLDSA44_PRIVATE_SEED_BYTES] = 4;
  augmented_entropy[MLDSA44_PRIVATE_SEED_BYTES + 1] = 4;

  uint8_t expanded_seed[K_RHO_BYTES + K_SIGMA_BYTES + K_K_BYTES];
  SHAKE256_buffer(expanded_seed, sizeof(expanded_seed), augmented_entropy,
                  sizeof(augmented_entropy));

  const uint8_t *const rho = expanded_seed;
  const uint8_t *const sigma = expanded_seed + K_RHO_BYTES;
  const uint8_t *const k = expanded_seed + K_RHO_BYTES + K_SIGMA_BYTES;

  memcpy(priv->rho, rho, sizeof(priv->rho));
  memcpy(priv->sigma, sigma, sizeof(priv->sigma));
  memcpy(priv->k, k, sizeof(priv->k));

  vector4_t s1_ntt;
  expand_s1(&s1_ntt, sigma);
  vector4_ntt(&s1_ntt);

  // It is safe for t1 or t0 to alias t because the underlying power2_round
  // takes its input by value, capturing it before any writes to the output
  // occur. t1 and t0 must be distinct.
  vector4_t *t = &priv->t0_ntt;
  matrix44_expand_mul(t, rho, &s1_ntt);
  vector4_inverse_ntt(t);
  vector4_t *const s2 = &s1_ntt;
  expand_s2(s2, sigma);
  vector4_add(t, t, s2);

  vector4_t *const t1 = &s1_ntt;
  vector4_power2_round(t1, &priv->t0_ntt, t);
  vector4_ntt(&priv->t0_ntt);

  memcpy(out_encoded_public_key, rho, K_RHO_BYTES);
  vector4_encode_10(&out_encoded_public_key[K_RHO_BYTES], t1);
}

// generate_priv_internal is marked noinline to prevent the compiler from
// inlining it, which would increase the peak stack usage of the caller.
static __attribute__((noinline)) void generate_priv_internal(
    private_key_t *out_priv, uint8_t out_public_key_hash[K_TR_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES]) {
  uint8_t encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES];
  generate_key_internal(encoded_public_key, out_priv, private_key_seed);
  if (out_public_key_hash != NULL) {
    SHAKE256_buffer(out_public_key_hash, K_TR_BYTES, encoded_public_key,
                    sizeof(encoded_public_key));
  }
}

// FIPS 204, Algorithm 7 (`ML-DSA.Sign_internal`).
static void sign_internal_with_mu(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const private_key_t *priv, const uint8_t mu[K_MU_BYTES],
    const uint8_t randomizer[MLDSA44_RANDOMIZER_BYTES]) {
  uint8_t rho_prime[K_RHO_PRIME_BYTES];
  shake256_ctxt_t shake256_ctxt;
  SHAKE256_init(&shake256_ctxt);
  SHAKE256_absorb(&shake256_ctxt, priv->k, sizeof(priv->k));
  SHAKE256_absorb(&shake256_ctxt, randomizer, MLDSA44_RANDOMIZER_BYTES);
  SHAKE256_absorb(&shake256_ctxt, mu, K_MU_BYTES);
  SHAKE256_squeeze(&shake256_ctxt, rho_prime, K_RHO_PRIME_BYTES);
  SHAKE256_free(&shake256_ctxt);

  uint8_t c_tilde[2 * LAMBDA_BYTES];
  vector4_t tmp;

  // kappa must not exceed 2^16/L. But the probability of it
  // exceeding even 1000 iterations is vanishingly small.
  for (size_t kappa = 0;; kappa += 4) {
    vector4_t *const w = &tmp;
    matrix44_expand_mul_mask(w, priv->rho, rho_prime, kappa);
    vector4_inverse_ntt(w);

    SHAKE256_init(&shake256_ctxt);
    SHAKE256_absorb(&shake256_ctxt, mu, K_MU_BYTES);
    // Encode each scalar of w1 individually and absorb into the c_tilde state.
    for (size_t i = 0; i < 4; i++) {
      uint8_t w1_encoded_part[192];
      scalar_t temp;
      scalar_high_bits_88(&temp, &w->v[i]);
      scalar_encode_6(w1_encoded_part, &temp);
      SHAKE256_absorb(&shake256_ctxt, w1_encoded_part, 192);
    }
    SHAKE256_squeeze(&shake256_ctxt, c_tilde, 2 * LAMBDA_BYTES);
    SHAKE256_free(&shake256_ctxt);

    scalar_t c_ntt;
    scalar_sample_in_ball_vartime(TAU, &c_ntt, c_tilde, sizeof(c_tilde));
    scalar_ntt(&c_ntt);

    // Encode c_tilde.
    memcpy(out_encoded_signature, c_tilde, 2 * LAMBDA_BYTES);

    // We compute z and update the bounds for each scalar in the vector
    // separately.
    uint32_t z_max = 0, r0_max = 0, ct0_max = 0;
    size_t h_ones = 0;
    uint8_t *z_output = &out_encoded_signature[2 * LAMBDA_BYTES];
    vector4_t *const h = &tmp;
    for (size_t i = 0; i < 4; i++) {
      scalar_t cs_i;
      expand_s1_ntt_mul_scalar(&cs_i, i, priv->sigma, &c_ntt);
      scalar_inverse_ntt(&cs_i);

      scalar_t z_i;
      scalar_expand_mask_17(&z_i, rho_prime, kappa, i);
      scalar_add(&z_i, &z_i, &cs_i);

      // Update z_max bound.
      scalar_max(&z_max, &z_i);

      // Encode z_i.
      scalar_encode_signed_18_17(z_output + i * 18 * K_DEGREE / 8, &z_i);

      expand_s2_ntt_mul_scalar(&cs_i, i, priv->sigma, &c_ntt);
      scalar_inverse_ntt(&cs_i);

      scalar_t r0_i;
      scalar_sub(&r0_i, &w->v[i], &cs_i);
      scalar_low_bits_88(&r0_i, &r0_i);

      // Update r0_max bound.
      scalar_max_signed(&r0_max, &r0_i);

      scalar_t *ct0_i = &r0_i;
      scalar_mul(ct0_i, &priv->t0_ntt.v[i], &c_ntt);
      scalar_inverse_ntt(ct0_i);
      scalar_make_hint_88(&h->v[i], ct0_i, &cs_i, &w->v[i]);

      // Update ct0_max bounds and h_ones count.
      scalar_max(&ct0_max, ct0_i);
      h_ones += scalar_count_ones(&h->v[i]);
    }

    // Leaking the fact that a signature was rejected is fine as the next
    // attempt at a signature will be (indistinguishable from) independent of
    // this one. Note we leak less than what is described by the paper; we do
    // not reveal which coefficient violated the bound, and we hide which of the
    // |z_max|, |r0_max|, |ct0_max|, or h_ones violated the bound.
    if (ct_ge(z_max, GAMMA1 - BETA) | ct_ge(r0_max, K_GAMMA_2 - BETA) |
        ct_ge(ct0_max, K_GAMMA_2) | ct_lt(OMEGA, (ct_uint32_t)h_ones)) {
      continue;
    }

    // Encode hint.
    uint8_t *hint_output = &out_encoded_signature[2 * LAMBDA_BYTES + 576 * 4];
    hint_bit_pack(hint_output, h);

    return;
  }
}

// FIPS 204, Algorithm 8 (`ML-DSA.Verify_internal`).
static int verify_internal_with_mu(
    const uint8_t encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES],
    const uint8_t encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t mu[K_MU_BYTES]) {
  uint8_t sig_c_tilde[2 * LAMBDA_BYTES];
  vector4_t z;
  hint_t h;
  vector4_t az_ntt;

  if (!decode_signature(sig_c_tilde, &z, &h, encoded_signature))
    return 0;

  // Compute ||z||_\infty and set z = NTT(z).
  uint32_t z_max = vector4_max(&z);
  vector4_ntt(&z);

  scalar_t c_ntt;
  scalar_sample_in_ball_vartime(TAU, &c_ntt, sig_c_tilde, sizeof(sig_c_tilde));
  scalar_ntt(&c_ntt);

  matrix44_expand_mul(&az_ntt, encoded_public_key, &z);

  // Since sign.z is no longer needed after the matrix multiplication, we reuse
  // its buffer to hold t1 and ct1_ntt (which eventually stores c * t1 * 2^d) to
  // save stack space.
  vector4_t *const t1 = &z;
  vector4_decode_10(t1, &encoded_public_key[K_RHO_BYTES]);
  vector4_t *const ct1_ntt = &z;
  vector4_scale_power2_round(ct1_ntt, t1);
  vector4_ntt(ct1_ntt);

  vector4_mul_scalar(ct1_ntt, ct1_ntt, &c_ntt);

  vector4_t *const w1 = &az_ntt;
  vector4_sub(w1, &az_ntt, ct1_ntt);
  vector4_inverse_ntt(w1);

  vector4_use_hint(w1, &h, w1);

  uint8_t c_tilde[2 * LAMBDA_BYTES];
  shake256_ctxt_t shake256_ctxt;
  SHAKE256_init(&shake256_ctxt);
  SHAKE256_absorb(&shake256_ctxt, mu, K_MU_BYTES);
  // Encode each scalar of w1 individually and absorb into the c_tilde state.
  for (size_t i = 0; i < 4; i++) {
    uint8_t w1_encoded_part[192];
    scalar_encode_6(w1_encoded_part, &w1->v[i]);
    SHAKE256_absorb(&shake256_ctxt, w1_encoded_part, 192);
  }
  SHAKE256_squeeze(&shake256_ctxt, c_tilde, 2 * LAMBDA_BYTES);
  SHAKE256_free(&shake256_ctxt);

  return z_max < (uint32_t)(GAMMA1 - BETA) &&
         memcmp(c_tilde, sig_c_tilde, 2 * LAMBDA_BYTES) == 0;
}

/* Public API. */

void mldsa44_tiny_pub_from_seed(
    uint8_t out_encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES]) {
  private_key_t priv;
  generate_key_internal(out_encoded_public_key, &priv, private_key_seed);
}

void mldsa44_tiny_sign(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES],
    const uint8_t randomizer[MLDSA44_RANDOMIZER_BYTES], const uint8_t *msg,
    size_t msg_len) {
  private_key_t priv;
  // Re-use the same buffer for tr (public key hash) as mu.
  uint8_t tr_mu[K_TR_BYTES];
  generate_priv_internal(&priv, tr_mu, private_key_seed);
  compute_mu_from_public_key_hash(tr_mu, tr_mu, NULL, 0, msg, msg_len);
  sign_internal_with_mu(out_encoded_signature, &priv, tr_mu, randomizer);
}

void mldsa44_tiny_sign_mu(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES],
    const uint8_t randomizer[MLDSA44_RANDOMIZER_BYTES],
    const uint8_t mu[K_MU_BYTES]) {
  private_key_t priv;
  generate_priv_internal(&priv, NULL, private_key_seed);
  sign_internal_with_mu(out_encoded_signature, &priv, mu, randomizer);
}

void mldsa44_tiny_sign_deterministic(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES],
    const uint8_t *msg, size_t msg_len) {
  private_key_t priv;
  // Re-use the same buffer for tr (public key hash) as mu.
  uint8_t tr_mu[K_TR_BYTES];
  generate_priv_internal(&priv, tr_mu, private_key_seed);
  uint8_t randomizer[MLDSA44_RANDOMIZER_BYTES];
  memset(randomizer, 0, MLDSA44_RANDOMIZER_BYTES);
  compute_mu_from_public_key_hash(tr_mu, tr_mu, NULL, 0, msg, msg_len);
  sign_internal_with_mu(out_encoded_signature, &priv, tr_mu, randomizer);
}

void mldsa44_tiny_sign_mu_deterministic(
    uint8_t out_encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t private_key_seed[MLDSA44_PRIVATE_SEED_BYTES],
    const uint8_t mu[K_MU_BYTES]) {
  private_key_t priv;
  uint8_t randomizer[MLDSA44_RANDOMIZER_BYTES];
  memset(randomizer, 0, MLDSA44_RANDOMIZER_BYTES);
  generate_priv_internal(&priv, NULL, private_key_seed);
  sign_internal_with_mu(out_encoded_signature, &priv, mu, randomizer);
}

int mldsa44_tiny_verify(
    const uint8_t encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES],
    const uint8_t encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t *msg, size_t msg_len) {
  uint8_t mu[K_MU_BYTES];
  compute_mu(mu, encoded_public_key, MLDSA44_PUBLIC_KEY_BYTES, NULL, 0, msg,
             msg_len);
  return verify_internal_with_mu(encoded_public_key, encoded_signature, mu);
}

int mldsa44_tiny_verify_mu(
    const uint8_t encoded_public_key[MLDSA44_PUBLIC_KEY_BYTES],
    const uint8_t encoded_signature[MLDSA44_SIGNATURE_BYTES],
    const uint8_t mu[K_MU_BYTES]) {
  return verify_internal_with_mu(encoded_public_key, encoded_signature, mu);
}
