/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 keygen OTBN app. */

.globl mldsa87_keygen

.section .text.start

/* Public interface. Direct implementation of the `ML-DSA.KeyGen_internal`
   function (Algorithm 6) of FIPS-204. */
mldsa87_keygen:
  addi x2, x0, 0
  jal x1, _keygen
  ecall

/* Test interface. Enables unmasking of values for inspection. */
_mldsa87_keygen_test:

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

  /*
   * The keygen function can be run in two modes:
   *
   *  - Random mode: Full execution of the keygen function with a randomly
   *    sampled RND string from EDN1.
   *
   *  - Deterministic mode: Full execution of the keygen function with XI set
   *    by the invoking program. This mode should only be used for testing
   *    purposes.
   */

  /* Mode identifiers, see `mldsa/mldsa.h`. */
  li x2, 0x5514edb7 /* Random */
  li x3, 0xfaacd725 /* Deterministic */

  /* Load the addresses of the mode and XI string. */
  la x4, mldsa87_keygen_mode
  la x5, mldsa87_keygen_xi_share0
  la x6, mldsa87_keygen_xi_share1

  /* Load the selected mode from DMEM. */
  lw x7, 0(x4)

  /* Save the instruction count and set the expected number of instructions
     for the determinstic mode branch. */
  csrrs x8, INSN_CNT, x0
  addi x9, x0, 3

  /* If the selected mode is deterministic, jump to the computation of hash of
     XI, otherwise sample the XI string from EDN1. */
  beq x3, x7, _hash_seed
  bne x2, x7, _fault

  /* Sample 32 bytes (two shares) of EDN1 randomness and store it to DMEM. */
  bn.wsrr w0, RND
  bn.sid x0, 0(x5)
  bn.xor w31, w31, w31 /* dummy */
  bn.wsrr w0, RND
  bn.sid x0, 0(x6)

  /* Set the expected number of instructions for the random branch. */
  addi x9, x0, 10

_hash_seed:

  /* Verify that the random or deterministic branch has run for the correct
     number of instructions. */
  csrrs x2, INSN_CNT, x0
  sub x2, x2, x8
  bne x2, x9, _fault

  /* Copy XI. */
  la x2, mldsa87_keygen_xi_share0
  la x3, mldsa87_keygen_xi_share1
  la x4, mldsa87_keygen_var_xi_share0
  la x5, mldsa87_keygen_var_xi_share1
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x4)
  bn.wsrr w0, URND /* dummy */
  bn.lid x0, 0(x3)
  bn.Sid x0, 0(x5)

  /* RHO, RHO_PRIME, K = Shake256(Xi). */
  la x2, mldsa87_keygen_var_xi_share0
  la x3, mldsa87_keygen_var_xi_share1
  la x4, mldsa87_keygen_var_rho
  la x5, mldsa87_keygen_var_rho_prime_share0
  la x6, mldsa87_keygen_var_rho_prime_share1
  la x7, mldsa87_keygen_sk_k_share0
  la x8, mldsa87_keygen_sk_k_share1
  jal x1, hash_seed

  /* Copy RHO. */
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

  ret

  unimp
_fault:
  unimp
  unimp
  unimp
