/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DS-87 keygen OTBN app. */

.globl mldsa87_keygen

.text

/* Public interface. Direct implementation of the `ML-DSA.KeyGen_internal`
   function (Algorithm 6) of FIPS-204. */
mldsa87_keygen:
  jal x1, _keygen
  ecall

/* Test interface. Enables unmasking of values for inspection. */
_mldsa87_keygen_test:
  jal x0, _keygen

/*
 * Direct implementation of the `ML-DSA.KeyGen_internal` function (Algorithm 6)
 * of FIPS-204.
 */
_keygen:
  /* Initialize stack and all-zero WDR. */
  la x31, stack
  bn.xor w31, w31, w31

  /* Load the ML-DSA parameters into the MOD register. */
  la x2, mldsa87_keygen_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* RHO, RHO_PRIME, K = Shake256(Xi). */
  la x2, mldsa87_keygen_xi_share0
  la x3, mldsa87_keygen_xi_share1
  la x4, mldsa87_keygen_pk_rho
  la x5, mldsa87_keygen_sk_rho_prime_share0
  la x6, mldsa87_keygen_sk_rho_prime_share1
  la x7, mldsa87_keygen_sk_k_share0
  la x8, mldsa87_keygen_sk_k_share1
  jal x1, hash_seed

  /* Sample and encode the S1 and S2 vectors. */
  la x2, mldsa87_keygen_sk_rho_prime_share0
  la x3, mldsa87_keygen_sk_rho_prime_share1
  la x4, mldsa87_keygen_sk_s1_share0
  la x5, mldsa87_keygen_sk_s1_share1
  la x6, mldsa87_keygen_sk_s2_share0
  la x7, mldsa87_keygen_sk_s2_share1
  la x8, mldsa87_keygen_poly_slot0
  la x9, mldsa87_keygen_poly_slot1
  jal x1, sample_s

  /* T = A * S1 + S2. */
  la x2, mldsa87_keygen_pk_rho
  la x3, mldsa87_keygen_sk_s1_share0
  la x4, mldsa87_keygen_sk_s1_share1
  la x5, mldsa87_keygen_sk_s2_share0
  la x6, mldsa87_keygen_sk_s2_share1
  la x7, mldsa87_keygen_vector_slot0
  la x8, mldsa87_keygen_vector_slot1
  la x9, mldsa87_keygen_poly_slot0
  la x10, mldsa87_keygen_poly_slot1
  la x11, mldsa87_keygen_poly_slot2
  jal x1, compute_t

  /* T0, T1 = Encode(Power2Round(T)). */
  la x2, mldsa87_keygen_vector_slot0
  la x3, mldsa87_keygen_vector_slot1
  la x4, mldsa87_keygen_sk_t0
  la x5, mldsa87_keygen_pk_t1
  la x6, mldsa87_keygen_poly_slot0
  la x7, mldsa87_keygen_poly_slot1
  jal x1, encode_t

  /* TR = Shake256(PK). */
  la x2, mldsa87_keygen_pk_rho
  la x3, mldsa87_keygen_sk_tr
  jal x1, hash_pk

  ret
