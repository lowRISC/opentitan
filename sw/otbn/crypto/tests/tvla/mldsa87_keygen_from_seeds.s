/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 keygen TVLA test harness.
   Executes the entire ML-DSA-87 Key Generation pipeline starting directly from
   the seeds (rho, rho_prime), skipping the initial SHAKE256(xi) derivation. */

.globl mldsa87_keygen_from_seeds

.section .text.start

mldsa87_keygen_from_seeds:
  /* Initialize stack and all-zero WDR. */
  la x31, stack
  bn.xor w31, w31, w31

  /* Load the ML-DSA parameters into the MOD register. */
  la x2, mldsa87_keygen_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* Copy RHO to PK and SK. */
  la x2, mldsa87_keygen_var_rho
  la x3, mldsa87_keygen_pk_rho
  la x4, mldsa87_keygen_sk_rho
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x3)
  bn.sid x0, 0(x4)

  /* Sample and encode the S1 and S2 vectors. */
  la x2, mldsa87_keygen_var_rho_prime_share0
  la x3, mldsa87_keygen_var_rho_prime_share1
  la x4, mldsa87_keygen_sk_s1_share0
  la x5, mldsa87_keygen_sk_s1_share1
  la x6, mldsa87_keygen_sk_s2_share0
  la x7, mldsa87_keygen_sk_s2_share1
  la x8, mldsa87_keygen_poly_slot0
  la x9, mldsa87_keygen_poly_slot1
  jal x1, sample_s

  /* T = A * S1 + S2. */
  la x2, mldsa87_keygen_var_rho
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

  ecall
