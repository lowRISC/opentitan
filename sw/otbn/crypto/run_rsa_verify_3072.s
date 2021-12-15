/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

/**
 * Standalone embeddable wrapper for 3072 bit RSA signature verification.
 * Performs either computation of Montgomery constants or modular
 * exponentiation, depending on mode.
 *
 * This file allocates space only for the pointers to large buffers, in order
 * to avoid including empty DMEM space in the binary. The caller must, before
 * executing this application, ensure that all input, output, and intermediate
 * buffers are allocated and non-overlapping, and that the pointers needed by
 * the given mode point to the correct locations.
 *
 * For computing constants (mode=1), the caller must allocate:
 *   - a 384-byte buffer holding the modulus at dmem[dptr_mod]
 *   - a 384-byte buffer for the output R^2 at dmem[dptr_rr]
 *   - a 32-byte buffer for the output m0_inv at dmem[dptr_m0_inv]
 *
 * For modular exponentiation (mode=2), the caller must allocate:
 *   - a 384-byte buffer holding the modulus at dmem[dptr_mod]
 *   - a 384-byte buffer holding the signature at dmem[dptr_sig]
 *   - a 384-byte buffer holding R^2 at dmem[dptr_rr]
 *   - a 32-byte buffer holding m0_inv at dmem[dptr_m0_inv]
 *   - a 384-byte buffer for the output at dmem[dptr_out_buf]
 *
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
 * @param[in] dmem[dptr_mod]: Modulus of the RSA public key
 * @param[out] dmem[dptr_rr]: Montgomery constant R^2 = (2^3072)^2 mod M
 * @param[out] dmem[dptr_m0inv]: Montgomery constant m0_inv = (-(M^-1)) mod 2^256
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
 * @param[in] dmem[exp]: Exponent of the RSA public key (must be 3 or F4=65537)
 * @param[in] dmem[dptr_mod]: Modulus of the RSA public key
 * @param[in] dmem[dptr_sig]: Signature to check against
 * @param[in] dmem[dptr_rr]: Montgomery constant R^2
 * @param[in] dmem[dptr_m0inv]: Montgomery constant m0_inv
 * @param[out] dmem[dptr_out_buf]: Recovered message digest (msg)
*/
modexp:
  /* Get the exponent: x3 <= dmem[exp] */
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

/* Mode (1=constants, 2=modexp) */
.globl mode
.balign 4
mode:
.zero 4

/* Exponent of the RSA-3072 key. Accepted values: 3 or F4=65537 */
.globl exp
.balign 4
exp:
.zero 4

/* Pointer to output buffer. */
.globl dptr_out_buf
.balign 4
dptr_out_buf:
.zero 4

/* Pointer to modulus. */
.globl dptr_mod
.balign 4
dptr_mod:
.zero 4

/* Pointer to signature. */
.globl dptr_sig
.balign 4
dptr_sig:
.zero 4

/* Pointer to the Montgomery transformation constant R^2. */
.globl dptr_rr
.balign 4
dptr_rr:
.zero 4

/* Pointer to the Montgomery constant -(M^-1) mod 2^256. */
.globl dptr_m0inv
.balign 4
dptr_m0inv:
.zero 4
