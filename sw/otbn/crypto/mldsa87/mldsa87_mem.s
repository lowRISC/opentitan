/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-DSA-87 memory file. */

.include "mldsa87.inc"

/*
 * All DMEM buffers live at fixed offsets in block. The layout is identical for
 * the `run_mldsa87` app and for usage as a library via `:mldsa87`. There are
 * three static regions `Secret Key`, `Public Key` and `Signature` shared
 * between the keygen, sign and verify operations. In addition, each operation
 * has a private scratch and overlays it onto the region it does not use.
 * This organisation results in the following layout matrix.
 *
 *          +------------+---------+---------+---------+
 *          | Region     | Keygen  | Sign    | Verify  |
 *          +============+=========+=========+=========+
 *          | Secret Key | Output  | Input   | Scratch |
 *          | Public Key | Output  | Scratch | Input   |
 *          | Signature  | Scratch | Output  | Input   |
 *          +------------+---------+---------+---------+
 *
 * DMEM (static block)
 * ==================
 *
 *  Offset   Buffer                     Overlays
 *          +-------------------------+
 *  0x0000  | mode                    |
 *  0x0020  | const_params            |
 *  0x0040  | const_gamma1_beta_bound |
 *  0x0060  | const_gamma2_beta_bound |
 *  0x0080  | mu                      |
 *  0x00c0  | stack                   |
 *          +=========================+  Secret Key / verify scratch
 *  0x01c0  | sk_rho                  |
 *  0x01e0  | sk_k_share0             |
 *  0x0200  | sk_k_share1             |
 *  0x0220  | sk_tr                   |
 *  0x0240  |                         |  +- verify_res_ok
 *  0x0260  | sk_s1_share0            |  |
 *  0x0280  |                         |  +- verify_res_c_tilde_prime
 *  0x02c0  |                         |  +- verify_var_rho
 *  0x0300  |                         |  +- verify_var_c
 *  0x0500  | sk_s1_share1            |  |
 *  0x0700  |                         |  +- verify_var_h
 *  0x07a0  | sk_s2_share0            |  |
 *  0x0860  |                         |  +- (end)
 *  0x0aa0  | sk_s2_share1            |
 *  0x0da0  | sk_t0                   |
 *          +=========================+  Public Key / sign scratch
 *  0x1aa0  | pk_rho                  |
 *  0x1ac0  | pk_t1                   |
 *  0x1ae0  |                         |  +- sign_rnd_share0
 *  0x1b00  |                         |  +- sign_rnd_share1
 *  0x1b20  |                         |  +- sign_kappa
 *  0x1b40  |                         |  +- sign_var_rho_prime_share0
 *  0x1ba0  |                         |  +- sign_var_rho_prime_share1
 *  0x1c00  |                         |  +- sign_var_rho
 *  0x1c40  |                         |  +- sign_var_w1_enc
 *  0x2040  |                         |  +- sign_var_c
 *  0x2440  |                         |  +- (end)
 *          +=========================+  Signature / poly slots / keygen scratch
 *  0x24c0  | sig_c_tilde             |
 *  0x2500  | sig_z                   |
 *  0x2520  |                         |  +- poly_slot0
 *  0x2920  |                         |  +- poly_slot1
 *  0x2d20  |                         |  +- poly_slot2
 *  0x3120  |                         |  +- poly_slot3
 *  0x3140  |                         |  |  +- keygen_xi_share0
 *  0x3160  |                         |  |  +- keygen_xi_share1
 *  0x3180  |                         |  |  +- keygen_var_xi_share0
 *  0x31c0  |                         |  |  +- keygen_var_xi_share1
 *  0x3200  |                         |  |  +- keygen_var_rho
 *  0x3240  |                         |  |  +- keygen_var_rho_prime_share0
 *  0x32a0  |                         |  |  +- keygen_var_rho_prime_share1
 *  0x3300  |                         |  |  +- (end)
 *  0x3520  |                         |  +- (end)
 *  0x3680  | sig_h                   |
 *  0x36e0  +-------------------------+
 *
 *  - Keygen uses poly slots 0-2 only. Its scratch lives in slot 3.
 *  - Sign generates Z last, after the last use of the poly slots. Its scratch
 *    lies outside `Signature` so that RND, KAPPA and RHO_PRIME survive the
 *    zeroing of Z between the throughout a double-sign invocation.
 *  - Verify decodes Z and H before touching any poly slot.
 *
 * DMEM (locally defined, shadowed by .weak declarations)
 * ======================================================
 *
 *          +---------------------------------+  Size  Defined in
 *          | const_zeta                      |  1024  mldsa87_ntt.s
 *          | const_zeta_inv                  |  1024  mldsa87_ntt.s
 *          | sample_in_ball_scratch          |    32  mldsa87_sample.s
 *          | const_sec_decompose_gamma2      |    32  mldsa87_gadgets.s
 *          | const_sec_decompose_alphas      |    32  mldsa87_gadgets.s
 *          | const_decompose_alphas          |    32  mldsa87_rounding.s
 *          | const_decompose_gamma2          |    32  mldsa87_rounding.s
 *          | const_decompose_q               |    32  mldsa87_rounding.s
 *          +---------------------------------+  2240
 *
 * Scratchpad
 * ==========
 *
 *          +-------------------------+
 *  0x0000  | vector_slot0            |  8 polynomials
 *  0x2000  | vector_slot1            |  8 polynomials
 *  0x4000  +-------------------------+
 */

/**
 * Declare a global DMEM buffer at a fixed offset.
 *
 * @param name Symbol name of the buffer.
 * @param off Byte offset of the buffer relative to `_mldsa87_dmem`.
 */
.macro mldsa87_buf name, off
  .globl \name
  .set \name, _mldsa87_dmem + \off
.endm

.data
.balign 32

_mldsa87_dmem:

/* Mode (4 bytes + 28 bytes padding). */
.zero 32

/*
 * q  = 8380417 = 2^23 - 2^13 + 1 (ML-DSA modulus)
 * mu = -q^-1 mod R (Montgomery constant)
 * f  = 256^-1 * R^2 mod q (INTT divisor time R in Montgomery domain)
 */
.word MLDSA87_Q /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* f */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* GAMMA1 - BETA = 2^19 - 120. */
.word MLDSA87_GAMMA1 - MLDSA87_BETA
.word MLDSA87_GAMMA1 - MLDSA87_BETA
.word MLDSA87_GAMMA1 - MLDSA87_BETA
.word MLDSA87_GAMMA1 - MLDSA87_BETA
.word MLDSA87_GAMMA1 - MLDSA87_BETA
.word MLDSA87_GAMMA1 - MLDSA87_BETA
.word MLDSA87_GAMMA1 - MLDSA87_BETA
.word MLDSA87_GAMMA1 - MLDSA87_BETA

/* GAMMA2 - BETA = ((Q - 1) / 32) - 120. */
.word MLDSA87_GAMMA2 - MLDSA87_BETA
.word MLDSA87_GAMMA2 - MLDSA87_BETA
.word MLDSA87_GAMMA2 - MLDSA87_BETA
.word MLDSA87_GAMMA2 - MLDSA87_BETA
.word MLDSA87_GAMMA2 - MLDSA87_BETA
.word MLDSA87_GAMMA2 - MLDSA87_BETA
.word MLDSA87_GAMMA2 - MLDSA87_BETA
.word MLDSA87_GAMMA2 - MLDSA87_BETA

/* .data buffers. */
.zero 0x36e0 - 0x80

/*
 * Shared (128 bytes).
 */

mldsa87_buf mldsa87_mode,                    0x0000 /* 4 + 28 padding */
mldsa87_buf mldsa87_const_params,            0x0020 /* 32 */
mldsa87_buf mldsa87_const_gamma1_beta_bound, 0x0040 /* 32 */
mldsa87_buf mldsa87_const_gamma2_beta_bound, 0x0060 /* 32 */
mldsa87_buf mldsa87_mu,                      0x0080 /* 64 */
mldsa87_buf mldsa87_stack,                   0x00c0 /* 256 */

/* Secret key (6368 bytes). */
mldsa87_buf mldsa87_sk_rho,                  0x01c0 /* 32 */
mldsa87_buf mldsa87_sk_k_share0,             0x01e0 /* 32 */
mldsa87_buf mldsa87_sk_k_share1,             0x0200 /* 32 */
mldsa87_buf mldsa87_sk_tr,                   0x0220 /* 64 */
mldsa87_buf mldsa87_sk_s1_share0,            0x0260 /* 672 */
mldsa87_buf mldsa87_sk_s1_share1,            0x0500 /* 672 */
mldsa87_buf mldsa87_sk_s2_share0,            0x07a0 /* 768 */
mldsa87_buf mldsa87_sk_s2_share1,            0x0aa0 /* 768 */
mldsa87_buf mldsa87_sk_t0,                   0x0da0 /* 3328 */

/* Public key (2592 bytes). */
mldsa87_buf mldsa87_pk_rho,                  0x1aa0 /* 32 */
mldsa87_buf mldsa87_pk_t1,                   0x1ac0 /* 2560 */

/* Signature (4640 bytes). */
mldsa87_buf mldsa87_sig_c_tilde,             0x24c0 /* 64 */
mldsa87_buf mldsa87_sig_z,                   0x2500 /* 4480 */
mldsa87_buf mldsa87_sig_h,                   0x3680 /* 83 + 13 padding */

/* Polynomial slots (inside SIG_Z). */
mldsa87_buf mldsa87_poly_slot0,              0x2520 /* 1024 */
mldsa87_buf mldsa87_poly_slot1,              0x2920 /* 1024 */
mldsa87_buf mldsa87_poly_slot2,              0x2d20 /* 1024 */
mldsa87_buf mldsa87_poly_slot3,              0x3120 /* 1024 */

/*
 * Keygen scratch (inside POLY_SLOT3).
 */

mldsa87_buf mldsa87_keygen_xi_share0,            0x3140 /* 32 */
mldsa87_buf mldsa87_keygen_xi_share1,            0x3160 /* 32 */
mldsa87_buf mldsa87_keygen_var_xi_share0,        0x3180 /* 34 + 30 padding */
mldsa87_buf mldsa87_keygen_var_xi_share1,        0x31c0 /* 34 + 30 padding */
mldsa87_buf mldsa87_keygen_var_rho,              0x3200 /* 34 + 30 padding */
mldsa87_buf mldsa87_keygen_var_rho_prime_share0, 0x3240 /* 66 + 30 padding */
mldsa87_buf mldsa87_keygen_var_rho_prime_share1, 0x32a0 /* 66 + 30 padding */

/*
 * Sign scratch (inside `Public Key`).
 */

mldsa87_buf mldsa87_sign_rnd_share0,             0x1ae0 /* 32 */
mldsa87_buf mldsa87_sign_rnd_share1,             0x1b00 /* 32 */
mldsa87_buf mldsa87_sign_kappa,                  0x1b20 /* 2 + 30 padding */
mldsa87_buf mldsa87_sign_var_rho_prime_share0,   0x1b40 /* 66 + 30 padding */
mldsa87_buf mldsa87_sign_var_rho_prime_share1,   0x1ba0 /* 66 + 30 padding */
mldsa87_buf mldsa87_sign_var_rho,                0x1c00 /* 34 + 30 padding */
mldsa87_buf mldsa87_sign_var_w1_enc,             0x1c40 /* 1024 */
mldsa87_buf mldsa87_sign_var_c,                  0x2040 /* 1024 */

/*
 * Verify scratch (inside `Secret Key`).
 */

mldsa87_buf mldsa87_verify_res_ok,               0x0240 /* 4 + 28 padding */
mldsa87_buf mldsa87_verify_res_c_tilde_prime,    0x0280 /* 64 */
mldsa87_buf mldsa87_verify_var_rho,              0x02c0 /* 34 + 30 padding */
mldsa87_buf mldsa87_verify_var_c,                0x0300 /* 1024 */
mldsa87_buf mldsa87_verify_var_h,                0x0700 /* 336 + 16 padding */

/*
 * Constants defined in source files.
 */

.weak mldsa87_const_zeta
.weak mldsa87_const_zeta_inv
.weak mldsa87_sample_in_ball_scratch
.weak mldsa87_const_sec_decompose_gamma2
.weak mldsa87_const_sec_decompose_alphas
.weak mldsa87_const_decompose_alphas
.weak mldsa87_const_decompose_gamma2
.weak mldsa87_const_decompose_q

.section .scratchpad
.balign 32

/*
 * Vector slots
 */

.globl mldsa87_vector_slot0
.globl mldsa87_vector_slot1

mldsa87_vector_slot0:
.zero 8192
mldsa87_vector_slot1:
.zero 8192
