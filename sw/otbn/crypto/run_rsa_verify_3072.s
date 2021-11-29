/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

/**
 * Standalone embeddable wrapper for 3072 bit RSA signature verification.
 * Performs either computation of Montgomery constants or modular
 * exponentiation, depending on mode.
 */
run_rsa_verify_3072:
  /* Get the mode input value: x3 <= mode */
  la       x2, mode
  lw       x3, 0(x2)

  /* if mode=1, compute constants (ends in ecall) */
  li       x2, 1
  beq      x3, x2, compute_constants

  /* if mode=2, run modexp (ends in ecall) */
  li       x2, 2
  beq      x3, x2, modexp

  /* Unexpected mode; fail */
  unimp

/**
 * Compute the two Montgomery constants for the given modulus.
 *
 * @param[in] dmem[in_mod]: Modulus of the RSA public key
 * @param[out] dmem[rr]: Montgomery constant R^2 = (2^3072)^2 mod M
 * @param[out] dmem[m0inv]: Montgomery constant m0_inv = (-(M^-1)) mod 2^256
*/
compute_constants:
  jal       x1, compute_rr
  jal       x1, compute_m0_inv
  ecall

/**
 * Run RSA-3072 modular exponentiation.
 *
 * Computes msg=(sig^e) mod M, where
 *          e is the public key exponent
 *          M is the public key modulus
 *          sig is the signature
 *
 * The result, msg, is the recovered message digest.
 *
 * @param[in] dmem[in_exp]: Exponent of the RSA public key (must be 3 or F4=65537)
 * @param[in] dmem[in_mod]: Modulus of the RSA public key
 * @param[in] dmem[in_buf]: Signature to check against
 * @param[in] dmem[rr]: Montgomery constant R^2
 * @param[in] dmem[m0inv]: Montgomery constant m0_inv
 * @param[out] dmem[out_buf]: Recovered message digest (msg)
*/
modexp:
  /* Get the exponent: x3 <= dmem[in_exp] */
  la       x2, in_exp
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
  /* e=3 exponentiation is unimplemented */
  unimp

.data

/* Mode (1=constants, 2=modexp) */
.globl mode
.balign 4
mode:
.zero 4

/* Exponent of the RSA-3072 key. Accepted values: 3 or F4=65537 */
.globl in_exp
.balign 4
in_exp:
.zero 4

/* Modulus of RSA-3072 key */
.globl in_mod
.balign 32
in_mod:
.zero 384

/* Montgomery constant m0' */
.globl m0inv
.balign 32
m0inv:
.zero 32

/* Squared Mongomery Radix RR = (2^3072)^2 mod N */
.globl rr
.balign 32
rr:
.zero 384

/* signature */
.globl in_buf
.balign 32
in_buf:
.zero 384
