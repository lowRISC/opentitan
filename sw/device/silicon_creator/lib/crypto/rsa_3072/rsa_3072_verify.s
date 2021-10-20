/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * OTBN app to run RSA-3072 verification and constant precomputation.
 */
run_rsa_3072:
  la    x2, mode
  lw    x2, 0(x2)

  li    x3, 1
  beq   x2, x3, precomp

  li    x3, 2
  beq   x2, x3, verify

  /* Mode is neither 1 (= precomp) nor 2 (= verify). Fail. */
  unimp

.text

/**
 * Precomputation of Montgomery constants R^2 and m0_inv.
 *
 * Expects the modulus (in_mod) to be pre-populated. Results will be stored in
 * in_rr and in_m0_inv.
 */
precomp:
  /* TODO: not yet implemented */
  unimp

/**
 * RSA-3072 signature verification.
 *
 * Expects the RSA signature (in_buf), constants (in_rr, in_m0inv) and modulus
 * (in_mod) to be pre-populated. Recovered message will be stored in out_buf.
 */
verify:
  /* run modular exponentiation */
  jal      x1, modexp_var_3072_f4

  ecall

.data

/* Operation mode (1 = precomp; 2 = verify) */
.globl mode
.balign 4
mode:
  .zero 4

/* Output buffer for the resulting, recovered message. */
.globl out_buf
.balign 512
out_buf:
  .zero 384

/* Input buffer for the modulus. */
.globl in_mod
.balign 512
in_mod:
  .zero 384

/* Input buffer for the signature. */
.globl in_buf
.balign 512
in_buf:
  .zero 384

/* Input buffer for the Montgomery transformation constant R^2. */
.globl in_rr
.balign 512
in_rr:
  .zero 384

/* The Montgomery constant. */
.globl in_m0inv
.balign 32
in_m0inv:
  .zero 32
