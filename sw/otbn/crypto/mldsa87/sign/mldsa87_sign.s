/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 sign OTBN app. */

.globl mldsa87_sign

.text

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

  /*
   * Calculate RHO_PRIME = H(K || RND || MU).
   */

  jal x1, xof_shake256_init

  /* Absorb both shares of K. */
  addi x20, x0, 32
  la x21, mldsa87_sign_sk_k_share0
  la x22, mldsa87_sign_sk_k_share1
  jal x1, xof_absorb

  /* Absorb RND. */
  addi x20, x0, 32
  la x21, mldsa87_sign_rnd
  addi x22, x0, 0
  jal x1, xof_absorb

  /* Absorb MU. */
  addi x20, x0, 64
  la x21, mldsa87_sign_msg_mu
  addi x22, x0, 0
  jal x1, xof_absorb

  jal x1, xof_process

  /* Squeeze both shares of RHO_PRIME. */
  la x2, mldsa87_sign_var_rho_prime_share0
  la x3, mldsa87_sign_var_rho_prime_share1
  addi x4, x0, 29
  addi x5, x0, 30

  loopi 2, 4
    jal x1, xof_squeeze32

    bn.sid x4, 0(x2++)
    bn.xor w31, w31, w31 /* dummy */
    bn.sid x5, 0(x3++)
    /* End of loop */

  jal x1, xof_finish

  /* Set the nonce to 0 (after the previous loop x2 points to the nonce). */
  sw x0, 0(x2)

_rej_loop:

  /* Compute W and place in the vector slots. */
  la x2, mldsa87_sign_vector_slot0
  la x3, mldsa87_sign_vector_slot1
  la x4, mldsa87_sign_sk_rho
  la x5, mldsa87_sign_var_rho_prime_share0
  la x6, mldsa87_sign_var_rho_prime_share1
  la x7, mldsa87_sign_poly_slot0
  la x8, mldsa87_sign_poly_slot1
  la x9, mldsa87_sign_poly_slot2
  jal x1, compute_w

  /* Decompose W into W0 (Vector slots 0, 1) and W1. */
  la x2, mldsa87_sign_vector_slot0
  la x3, mldsa87_sign_vector_slot1
  la x4, mldsa87_sign_var_w1_enc
  la x5, mldsa87_sign_poly_slot0
  jal x1, decompose_w

  /* Compute C_TILDE. */
  la x2, mldsa87_sign_msg_mu
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
  la x4, mldsa87_sign_var_c
  la x5, mldsa87_sign_sk_s1_share0
  la x6, mldsa87_sign_sk_s1_share1
  la x7, mldsa87_sign_const_gamma1_beta_bound
  la x8, mldsa87_sign_vector_slot1
  la x9, mldsa87_sign_poly_slot0
  la x10, mldsa87_sign_poly_slot1
  la x11, mldsa87_sign_poly_slot2
  la x12, mldsa87_sign_poly_slot3
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
 * otherwise increment the nonce and jump back to the beginning of the
 * rejection loop.
 */
_rejection_check:
  bn.cmp w0, w31, FG0
  csrrs x2, FG0, x0
  andi x2, x2, 8
  bne x2, x0, _rejection_check_increment_nonce
  ret
_rejection_check_increment_nonce:
  la x2, mldsa87_sign_var_rho_prime_share0
  lw x3, 64(x2)
  addi x3, x3, 7
  sw x3, 64(x2)
  xor x0, x0, x1 /* Pop address from call stack */
  jal x0, _rej_loop
