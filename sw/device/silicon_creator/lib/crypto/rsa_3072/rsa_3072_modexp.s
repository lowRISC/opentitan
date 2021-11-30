/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * OTBN app to compute R^2 and then run RSA-3072 modexp.
 *
 * Expects the RSA signature (in_buf), constant m0_inv (in_m0inv) and modulus
 * (in_mod) to be pre-populated. Recovered message will be stored in out_buf.
 */
run_rsa_3072:
  /* Compute R^2 and store in in_rr */
  jal      x1, precomp_rr

  /* Run modular exponentiation and store the result in out_buf */
  jal      x1, modexp_var_3072_f4

  ecall

.text

.data

/* Output buffer for the resulting, recovered message. */
.globl out_buf
.balign 32
out_buf:
  .zero 384

/* Input buffer for the modulus. */
.globl in_mod
.balign 32
in_mod:
  .zero 384

/* Input buffer for the signature. */
.globl in_buf
.balign 32
in_buf:
  .zero 384

/* Working buffer for the Montgomery transformation constant R^2. */
.globl in_rr
.balign 32
in_rr:
  .zero 384

/* Input buffer for the Montgomery constant. */
.globl in_m0inv
.balign 32
in_m0inv:
  .zero 32
