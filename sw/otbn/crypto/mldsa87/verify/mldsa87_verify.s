/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 verify OTBN app. */

.globl mldsa87_verify

.section .text.start

/*
 * Direct implementation of the `ML-DSA.Verify_internal` function (Algorithm 8)
 * of FIPS-204.
 */
mldsa87_verify:
  /* Initialize stack and all-zero WDR. */
  la x31, stack
  bn.xor w31, w31, w31

  /* Load the ML-DSA parameters into the MOD register. */
  la x2, mldsa87_verify_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* Copy rho. */
  la x2, mldsa87_verify_pk_rho
  la x3, mldsa87_verify_var_rho
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x3)

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

  /* Check the validity of the hint. */
  la x2, mldsa87_verify_var_h
  jal x1, check_hint

  bn.cmp w0, w31, FG0
  csrrs x2, FG0, x0
  andi x2, x2, 0x8
  bne x2, x0, _mldsa87_verify_failure

  /* Sample the challenge polynomial C. */
  la x2, mldsa87_verify_var_c
  la x3, mldsa87_verify_sig_c_tilde
  jal x1, sample_in_ball

  /* Compute W_approx. */
  la x2, mldsa87_verify_var_rho
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
  la x2, mldsa87_verify_mu
  la x3, mldsa87_verify_vector_slot1
  la x4, mldsa87_verify_res_c_tilde_prime
  jal x1, challenge_hash

/*
 * Hardened values to encode successful/unsuccessful run of the verification
 * routine. A positive run means that no error condition lead to an early exit.
 * The ultimate comparison of the provided and generated C_TILDE values is
 * performed outside of the OTBN.
 *
 * Encoding generated with
 *
 *  ./util/design/sparse-fsm-encode.py -d 21 -m 2 -n 32 -s 3404539173 \
 *    --language=c --avoid-zero
 */
_mldsa87_verify_success:
  li x2, 0x7baf73d2
  la x3, mldsa87_verify_res_ok
  sw x2, 0(x3)
  ecall
_mldsa87_verify_failure:
  li x2, 0xadf1aebd
  la x3, mldsa87_verify_res_ok
  sw x2, 0(x3)
  ecall
