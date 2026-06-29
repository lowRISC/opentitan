/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 verify memory file. */

.data
.balign 32

/*
 * Public key
 */

.globl mldsa87_verify_pk_t1
.globl mldsa87_verify_pk_rho

mldsa87_verify_pk_t1:
.zero 2560
mldsa87_verify_pk_rho:
.zero 32
.zero 32 /* Padding */

/*
 * Signature
 */

.globl mldsa87_verify_sig_c_tilde
.globl mldsa87_verify_sig_z
.globl mldsa87_verify_sig_mu
.globl mldsa87_verify_sig_h

mldsa87_verify_sig_c_tilde:
.zero 64
mldsa87_verify_sig_z:
.zero 4480
mldsa87_verify_sig_mu:
.zero 64
mldsa87_verify_sig_h:
.zero 83
.zero 13 /* Padding */

/*
 * Verification result
 */

.globl mldsa87_verify_res_ok
.globl mldsa87_verify_c_tilde_prime

mldsa87_verify_res_ok:
.zero 4
.zero 28 /* Padding */
mldsa87_verify_res_c_tilde_prime:
.zero 64

/*
 * Intermediate variables
 */

.globl mldsa87_verify_var_c
.globl mldsa87_verify_var_h

/* Challenge polynomial */
mldsa87_verify_var_c:
.zero 1024
/* Encoded hint in intermediate representation. */
mldsa87_verify_var_h:
.zero 336
.zero 16 /* Padding */

/*
 * Polynomial slots
 */

.globl mldsa87_verify_poly_slot0
.globl mldsa87_verify_poly_slot1
.globl mldsa87_verify_poly_slot2

mldsa87_verify_poly_slot0:
.zero 1024
mldsa87_verify_poly_slot1:
.zero 1024
mldsa87_verify_poly_slot2:
.zero 1024

/*
 * Constants
 */

.globl mldsa87_verify_const_params
.globl mldsa87_verify_const_gamma1_beta_bound

/*
 * q  = 8380417 = 2^23 - 2^13 + 1 (ML-DSA modulus)
 * mu = -q^-1 mod R (Montgomery constant)
 * f  = 256^-1 * R^2 mod q (INTT divisor time R in Montgomery domain)
 */
mldsa87_verify_const_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* f */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* GAMMA1 - BETA = 2^19 - 120. */
mldsa87_verify_const_gamma1_beta_bound:
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88

.globl stack

stack:
.zero 256

.section .scratchpad
.balign 32

/*
 * Vector slots
 */

.globl mldsa87_verify_vector_slot0
.globl mldsa87_verify_vector_slot1

mldsa87_verify_vector_slot0:
.zero 8192
mldsa87_verify_vector_slot1:
.zero 8192
