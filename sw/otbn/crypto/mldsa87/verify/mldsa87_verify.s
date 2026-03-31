/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 verify OTBN app. */

.globl mldsa87_verify

.text

/*
 * Direct implementation of the `ML-DSA.Verify_internal` function (Algorithm 8)
 * of FIPS-204.
 */
mldsa87_verify:

  /* Decode the signature blob. */
  la x2, mldsa87_verify_sig_h
  la x3, mldsa87_verify_var_h
  la x4, mldsa87_verify_sig_z
  la x5, mldsa87_verify_vector_slot0
  jal x1, sig_decode

  /* Check the infinity norm of Z. */
  la x2, mldsa87_verify_vector_slot0
  la x3, mldsa87_verify_const_gamma1_beta_bound
  la x4, mldsa87_verify_poly_slot0
  jal x1, check_infinity_norm_z

  bn.cmp w0, w31, FG0
  csrrs x2, FG0, x0
  andi x2, x2, 0x8
  bne x2, x0, _mldsa87_verify_failure

  /* Sample the challenge polynomial C. */
  la x2, mldsa87_verify_var_c
  la x3, mldsa87_verify_sig_c_tilde
  jal x1, sample_in_ball

  /* Compute W_approx. */
  la x2, mldsa87_verify_pk_rho
  la x3, mldsa87_verify_vector_slot0
  la x4, mldsa87_verify_var_c
  la x5, mldsa87_verify_pk_t1
  la x6, mldsa87_verify_vector_slot1
  la x7, mldsa87_verify_poly_slot0
  jal x1, compute_w_approx

  /* Apply the hint to W_approx. */
  la x2, mldsa87_verify_vector_slot1
  la x3, mldsa87_verify_var_h
  la x4, mldsa87_verify_poly_slot0
  la x5, mldsa87_verify_poly_slot1
  jal x1, use_hint

  /* Recompute the challenge hash. */
  la x2, mldsa87_verify_sig_mu
  la x3, mldsa87_verify_vector_slot1
  la x4, mldsa87_verify_var_c
  jal x1, challenge_hash

  /* Compare the calculate challenge hash to c_tilde of the signature. */
  la x2, mldsa87_verify_sig_c_tilde
  la x3, mldsa87_verify_var_c
  addi x4, x0, 1
  addi x5, x0, 2
  bn.subi w0, w31, 1

  bn.lid x4, 0(x2++)
  bn.lid x5, 0(x3++)
  bn.cmp w1, w2, FG0
  bn.sel w0, w0, w31, FG0.Z

  bn.lid x4, 0(x2++)
  bn.lid x5, 0(x3++)
  bn.cmp w1, w2, FG0
  bn.sel w0, w0, w31, FG0.Z

  bn.cmp w0, w31, FG0
  csrrs x2, FG0, x0
  andi x2, x2, 0x8
  bne x2, x0, _mldsa87_verify_failure

/* End of the application, write the verify result to memory and exit. */
_mldsa87_verify_success:
  la x2, mldsa87_verify_result
  bn.subi w0, w31, 1
  bn.sid x0, 0(x2)
  ecall
_mldsa87_verify_failure:
  la x2, mldsa87_verify_result
  bn.xor w0, w0, w0
  bn.sid x0, 0(x2)
  ecall
