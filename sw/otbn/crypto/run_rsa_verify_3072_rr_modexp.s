/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

/**
 * Standalone embeddable wrapper for 3072 bit RSA signature verification.
 *
 * Uses the OTBN RSA 3072-bit only modular exponentiation implementation to
 * obtain the message (digest) from an input signature. Assumes that the
 * Montgomery constant m0_inv is provided, but computes the RR constant on the
 * fly.
 *
 * This file allocates space only for the pointers to large buffers, in order
 * to avoid including empty DMEM space in the binary. The caller must, before
 * executing this application, ensure that all input, output, and intermediate
 * buffers are allocated and non-overlapping, and that all pointers point to
 * the correct locations.
 *
 * @param[in] dmem[exp]: Exponent of the RSA public key (must be 3 or F4=65537)
 * @param[in] dmem[dptr_mod]: Modulus of the RSA public key
 * @param[in] dmem[dptr_sig]: Signature to check against
 * @param[in] dmem[dptr_m0inv]: Montgomery constant (-(M^-1)) mod 2^256
 * @param[in] dmem[dptr_rr]: Pre-allocated 384-byte buffer for R^2
 * @param[out] dmem[dptr_out_buf]: Recovered message digest
 */
run_rsa_verify_3072:

  /* Compute R^2 (same for both exponents): dmem[rr] <= R^2 */
  jal      x1, compute_rr

  /* Get the exponent: x3 <= dmem[in_exp] */
  la       x2, exp
  lw       x3, 0(x2)

  /* Call a modexp implementation matching the exponent.
     Both modexp implementations end in ecall. */
  li       x2, 3
  beq      x3, x2, modexp_3
  li       x2, 65537
  beq      x3, x2, modexp_f4

  /* Unexpected exponent; fail */
  unimp

modexp_f4:
  /* run modular exponentiation */
  jal      x1, modexp_var_3072_f4

  ecall

modexp_3:
  /* run modular exponentiation */
  jal      x1, modexp_var_3072_3

  ecall

.data

/* Exponent of the RSA-3072 key. Accepted values: 3 or F4=65537 */
.globl exp
.balign 4
exp:
.zero 4

/* Pointer to output buffer (384 bytes). */
.globl dptr_out_buf
.balign 4
dptr_out_buf:
.zero 4

/* Pointer to modulus (384 bytes). */
.globl dptr_mod
.balign 4
dptr_mod:
.zero 4

/* Pointer to signature (384 bytes). */
.globl dptr_sig
.balign 4
dptr_sig:
.zero 4

/* Pointer to the Montgomery transformation constant R^2 (384 bytes). */
.globl dptr_rr
.balign 4
dptr_rr:
.zero 4

/* Pointer to the Montgomery constant -(M^-1) mod 2^256 (32 bytes). */
.globl dptr_m0inv
.balign 4
dptr_m0inv:
.zero 4
