/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 keygen memory file. */

.data
.balign 32

/*
 * Seed
 */

.globl mldsa87_keygen_xi_share0
.globl mldsa87_keygen_xi_share1

mldsa87_keygen_xi_share0:
.zero 34
.zero 30 /* Padding */
mldsa87_keygen_xi_share1:
.zero 34
.zero 30 /* Padding */

/*
 * Public key
 */

.globl mldsa87_keygen_pk_rho
.globl mldsa87_keygen_pk_t1

mldsa87_keygen_pk_rho:
.zero 32
mldsa87_keygen_pk_t1:
.zero 2560

/*
 * Secret key
 */

.globl mldsa87_keygen_sk_rho_prime_share0
.globl mldsa87_keygen_sk_rho_prime_share1
.globl mldsa87_keygen_sk_k_share0
.globl mldsa87_keygen_sk_k_share1
.globl mldsa87_keygen_sk_tr
.globl mldsa87_keygen_sk_s1_share0
.globl mldsa87_keygen_sk_s1_share1
.globl mldsa87_keygen_sk_s2_share0
.globl mldsa87_keygen_sk_s2_share1
.globl mldsa87_keygen_sk_t0

mldsa87_keygen_sk_rho_prime_share0:
.zero 66
.zero 30 /* Padding */
mldsa87_keygen_sk_rho_prime_share1:
.zero 66
.zero 30 /* Padding */
mldsa87_keygen_sk_k_share0:
.zero 32
mldsa87_keygen_sk_k_share1:
.zero 32
mldsa87_keygen_sk_tr:
.zero 64
mldsa87_keygen_sk_s1_share0:
.zero 672
mldsa87_keygen_sk_s1_share1:
.zero 672
mldsa87_keygen_sk_s2_share0:
.zero 768
mldsa87_keygen_sk_s2_share1:
.zero 768
mldsa87_keygen_sk_t0:
.zero 3328

/*
 * Polynomial Slots
 */

.globl mldsa87_keygen_poly_slot0
.globl mldsa87_keygen_poly_slot1
.globl mldsa87_keygen_poly_slot2

/* Slots */
mldsa87_keygen_poly_slot0:
.zero 1024
mldsa87_keygen_poly_slot1:
.zero 1024
mldsa87_keygen_poly_slot2:
.zero 1024

/*
 * Constants
 */

.globl mldsa87_keygen_const_params

/*
 * q  = 8380417 = 2^23 - 2^13 + 1 (ML-DSA modulus)
 * mu = -q^-1 mod R (Montgomery constant)
 * f  = 256^-1 * R^2 mod q (INTT divisor time R in Montgomery domain)
 */
mldsa87_keygen_const_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* f */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000


.globl stack

stack:
.zero 256

.section .scratchpad
.balign 32

/*
 * Vector slots
 */

.globl mldsa87_keygen_vector_slot0
.globl mldsa87_keygen_vector_slot1

mldsa87_keygen_vector_slot0:
.zero 8192
mldsa87_keygen_vector_slot1:
.zero 8192
