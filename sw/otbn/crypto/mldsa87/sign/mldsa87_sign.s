/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 sign OTBN app. */

.globl mldsa87_sign

.section .text.start

/*
 * Direct implementation of the `ML-DSA.sign_internal` function (Algorithm 7)
 * of FIPS-204.
 */
mldsa87_sign:
  /* Initialize stack and all-zero WDR. */
  la x31, stack
  bn.xor w31, w31, w31

  /* Load the ML-DSA parameters into the MOD register. */
  la x2, mldsa87_sign_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* Copy RHO. */
  la x2, mldsa87_sign_sk_rho
  la x3, mldsa87_sign_var_rho
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x3)

  /*
   * The sign function can be run in three modes:
   *
   *  - Abridged mode: Skips the computation of the mask seed RHO_PRIME and
   *    does not set the randomness string RND. The current purpose of this
   *    mode is the recalculation of a prior last rejection loop. This mode
   *    assumes that the memory (specifically secret key, RND and KAPPA) are
   *    not cleared between invocations of the app.
   *
   *  - Random mode: Full execution of the sign function with a randomly
   *    sampled RND string from EDN1.
   *
   *  - Deterministic mode: Full execution of the sign function with RND set to
   *    0. This mode should only be used for testing purposes.
   */

  /* Mode identifiers, see `include/mldsa.h` and `mldsa/mldsa.h`. */
  li x2, 0x29d8e5c9 /* Abridged */
  li x3, 0x7138777c /* Random */
  li x4, 0x8accea7f /* Deterministic */

  /* Load the addresses of the mode and RND string. */
  la x5, mldsa87_sign_mode
  la x6, mldsa87_sign_rnd

  /* Check if the abridged mode is selected and jump directly into the
     rejection loop. */
  lw x7, 0(x5)
  beq x2, x7, _rej_loop

  /* Save the instruction count and set the expected number of instructions
     for the random mode branch. */
  csrrs x8, INSN_CNT, x0
  addi x9, x0, 5

  /* Sample 32 byte of EDN1 randomness and store it to DMEM. Regardless of
     the selected mode (random or deterministic) this is always executed. */
  bn.wsrr w0, RND
  bn.sid x0, 0(x6)

  /* If the selected mode is random, jump to the computation of RHO_PRIME,
     otherwise set the RND string to 0. */
  beq x3, x7, _compute_rho_prime
  bne x4, x7, _fault /* sanity check */

  /* Set RND to 0 in DMEM. */
  bn.xor w0, w0, w0
  bn.sid x0, 0(x6)

  /* Set the expected number of instructions for the deterministic branch. */
  addi x9, x0, 9

_compute_rho_prime:

  /* Verify that the random or deterministic branch has run for the correct
     number of instructions. */
  csrrs x2, INSN_CNT, x0
  sub x2, x2, x8
  bne x2, x9, _fault

  /* Calculate RHO_PRIME = H(K || RND || MU). */
  la x2, mldsa87_sign_sk_k_share0
  la x3, mldsa87_sign_sk_k_share1
  la x4, mldsa87_sign_rnd
  la x5, mldsa87_sign_mu
  la x6, mldsa87_sign_var_rho_prime_share0
  la x7, mldsa87_sign_var_rho_prime_share1
  jal x1, compute_rho_prime

  /* Set KAPPA to 0. */
  bn.xor w0, w0, w0
  la x2, mldsa87_sign_kappa
  bn.sid x0, 0(x2)

_rej_loop:

  /* Compute W and place in the vector slots. */
  la x2, mldsa87_sign_vector_slot0
  la x3, mldsa87_sign_vector_slot1
  la x4, mldsa87_sign_var_rho
  la x5, mldsa87_sign_var_rho_prime_share0
  la x6, mldsa87_sign_var_rho_prime_share1
  la x7, mldsa87_sign_kappa
  la x8, mldsa87_sign_poly_slot0
  jal x1, compute_w

  /* Decompose W into W0 (Vector slots 0, 1) and W1. */
  la x2, mldsa87_sign_vector_slot0
  la x3, mldsa87_sign_vector_slot1
  la x4, mldsa87_sign_var_w1_enc
  la x5, mldsa87_sign_poly_slot0
  jal x1, decompose_w

  /* Compute C_TILDE. */
  la x2, mldsa87_sign_mu
  la x3, mldsa87_sign_var_w1_enc
  la x4, mldsa87_sign_sig_c_tilde
  jal x1, challenge_hash

  /* Sample the challenge polynomial C and map it to the NTT domain. */
  la x2, mldsa87_sign_var_c
  la x3, mldsa87_sign_sig_c_tilde
  jal x1, sample_in_ball

  la x2, mldsa87_sign_var_c
  la x3, mldsa87_sign_var_c
  jal x1, ntt

  /* Compute R0 and place in vector slot 0. */
  la x2, mldsa87_sign_vector_slot0
  la x3, mldsa87_sign_vector_slot1
  la x4, mldsa87_sign_var_c
  la x5, mldsa87_sign_sk_s2_share0
  la x6, mldsa87_sign_sk_s2_share1
  la x7, mldsa87_sign_const_gamma2_beta_bound
  la x8, mldsa87_sign_poly_slot0
  la x9, mldsa87_sign_poly_slot1
  jal x1, compute_r0
  jal x1, _rejection_check

  /* Compute X0 and place in vector slot 0. */
  la x2, mldsa87_sign_vector_slot0
  la x3, mldsa87_sign_var_c
  la x4, mldsa87_sign_sk_t0
  la x5, mldsa87_sign_poly_slot0
  jal x1, compute_x0

  /* Compute Z and place in vector slot 1. */
  la x2, mldsa87_sign_var_rho_prime_share0
  la x3, mldsa87_sign_var_rho_prime_share1
  la x4, mldsa87_sign_kappa
  la x5, mldsa87_sign_var_c
  la x6, mldsa87_sign_sk_s1_share0
  la x7, mldsa87_sign_sk_s1_share1
  la x8, mldsa87_sign_const_gamma1_beta_bound
  la x9, mldsa87_sign_vector_slot1
  la x10, mldsa87_sign_poly_slot0
  jal x1, compute_z
  jal x1, _rejection_check

  /* Compute the hint H and place in vector slot 0. */
  la x2, mldsa87_sign_vector_slot0
  la x3, mldsa87_sign_var_w1_enc
  la x4, mldsa87_sign_poly_slot0
  jal x1, make_hint

  /* Make sure the Hamming weight of the hint is not too large. */
  la x2, mldsa87_sign_vector_slot0
  jal x1, hw_check_hint
  jal x1, _rejection_check

  /* Compress the hint. */
  la x2, mldsa87_sign_vector_slot0
  la x3, mldsa87_sign_sig_h
  la x4, mldsa87_sign_poly_slot0
  jal x1, compress_hint

  /* Encode the signature vector Z. */
  la x2, mldsa87_sign_vector_slot1
  la x3, mldsa87_sign_sig_z
  loopi 7, 3
    jal x1, encode_z
    addi x2, x2, 1024
    addi x3, x3, 640
    /* End of loop */

  ecall

/*
 * Check whether the value in w0 is not 0, if so return to the routine,
 * otherwise increment KAPPA and jump back to the beginning of the rejection
 * loop.
 */
_rejection_check:
  bn.cmp w0, w31, FG0
  csrrs x2, FG0, x0
  andi x2, x2, 8
  bne x2, x0, _rejection_check_increment_kappa
  ret
_rejection_check_increment_kappa:
  la x2, mldsa87_sign_kappa
  lw x3, 0(x2)
  addi x3, x3, 7
  sw x3, 0(x2)
  xor x0, x0, x1 /* Pop address from call stack */
  jal x0, _rej_loop
_fault:
  unimp
  unimp
  unimp
