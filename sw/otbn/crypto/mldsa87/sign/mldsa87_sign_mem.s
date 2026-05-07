/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 sign memory file. */

.data
.balign 32

/*
 * Randomness
 */

.globl mldsa87_sign_rnd

mldsa87_sign_rnd:
.zero 32

/*
 * Secret key
 */

.globl mldsa87_sign_sk_k_share0
.globl mldsa87_sign_sk_k_share1
.globl mldsa87_sign_sk_s1_share0
.globl mldsa87_sign_sk_s1_share1
.globl mldsa87_sign_sk_s2_share0
.globl mldsa87_sign_sk_s2_share1
.globl mldsa87_sign_sk_t0
.globl mldsa87_sign_sk_rho

mldsa87_sign_sig_z:
mldsa87_sign_sk_k_share0:
.zero 32
mldsa87_sign_sk_k_share1:
.zero 32
mldsa87_sign_sk_s1_share0:
.zero 672
mldsa87_sign_sk_s1_share1:
.zero 672
mldsa87_sign_sk_s2_share0:
.zero 768
mldsa87_sign_sk_s2_share1:
.zero 768
mldsa87_sign_sk_t0:
.zero 3328
mldsa87_sign_sk_rho:
.zero 32
.zero 32 /* Padding */

/*
 * Message
 */

.globl mldsa87_sign_msg_mu

mldsa87_sign_msg_mu:
.zero 64

/*
 * Signature
 */

.globl mldsa87_sign_sig_c_tilde
.globl mldsa87_sign_sig_h
.globl mldsa87_sign_sig_z

mldsa87_sign_sig_c_tilde:
.zero 64
mldsa87_sign_sig_h:
.zero 83
.zero 13 /* Padding */

/* For space reasons the the location of the encoded Z vector overlaps with the
   the secret key section. */

/*
 * Intermediate variables
 */

.globl mldsa87_sign_var_w1_enc
.globl mldsa87_sign_var_c
.globl mldsa87_sign_var_rho_prime_share0
.globl mldsa87_sign_var_rho_prime_share1

mldsa87_sign_var_w1_enc:
.zero 1024
mldsa87_sign_var_c:
.zero 1024
mldsa87_sign_var_rho_prime_share0:
.zero 66
.zero 30 /* Padding */
mldsa87_sign_var_rho_prime_share1:
.zero 66
.zero 30 /* Padding */

/*
 * Polynomial Slots
 */

.globl mldsa87_sign_poly_slot0
.globl mldsa87_sign_poly_slot1
.globl mldsa87_sign_poly_slot2
.globl mldsa87_sign_poly_slot3

mldsa87_sign_poly_slot0:
.zero 1024
mldsa87_sign_poly_slot1:
.zero 1024
mldsa87_sign_poly_slot2:
.zero 1024
mldsa87_sign_poly_slot3:
.zero 1024

/*
 * Constants
 */

.globl mldsa87_sign_const_params
.globl mldsa87_sign_const_gamma1_beta_bound
.globl mldsa87_sign_const_gamma2_beta_bound

/*
 * q  = 8380417 = 2^23 - 2^13 + 1 (ML-DSA modulus)
 * mu = -q^-1 mod R (Montgomery constant)
 * f  = 256^-1 * R^2 mod q (INTT divisor time R in Montgomery domain)
 */
mldsa87_sign_const_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* f */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* GAMMA1 - BETA = 2^19 - 120. */
mldsa87_sign_const_gamma1_beta_bound:
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88
.word 0x0007ff88

/* GAMMA2 - BETA = ((Q - 1) / 32) - 120. */
mldsa87_sign_const_gamma2_beta_bound:
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88
.word 0x0003fe88

.globl stack

stack:
.zero 256

.section .scratchpad
.balign 32

/*
 * Vector slots
 */

mldsa87_sign_vector_slot0:
.zero 8192
mldsa87_sign_vector_slot1:
.zero 8192
