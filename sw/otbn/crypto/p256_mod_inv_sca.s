/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Wrapper specifically for SCA/formal analysis of p256 modular inversion.
 *
 * This routine would never normally be exposed, but it's helpful for SCA to
 * analyze it in isolation.
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Load modulus and Barrett constant.
       w28 <= u, Barrett constant for n
       w29 <= n, p256 curve order
       MOD <= n */
  li        x2, 28
  la        x3, p256_u_n
  bn.lid    x2, 0(x3)
  li        x2, 29
  la        x3, p256_n
  bn.lid    x2, 0(x3)
  bn.wsrw   MOD, w29

  /* Load first share of input.
       w0, w1 <= dmem[k0] */
  la        x16, k0
  li        x2, 0
  bn.lid    x2, 0(x16++)
  li        x2, 1
  bn.lid    x2, 0(x16)

  /* Load second share of input.
       w2, w3 <= dmem[k1] */
  la        x16, k1
  li        x2, 2
  bn.lid    x2, 0(x16++)
  li        x2, 3
  bn.lid    x2, 0(x16)

  /* NOTE: the masking logic is written to mimic the version in `p256_sign`
     from p256.s; see the documentation of that function for details. */

  /* Generate a random 127-bit number.
       w4 <= URND()[255:129] */
  bn.wsrr  w4, URND
  bn.rshi  w4, w31, w4 >> 129

  /* Add 1 to get a 128-bit nonzero scalar for masking.
       w4 <= w4 + 1 = alpha */
  bn.addi  w4, w4, 1

  /* Store masking parameter. */
  li        x2, 4
  la        x3, alpha
  bn.sid    x2, 0(x3)

  /* w0 <= ([w0,w1] * w4) mod n = (k0 * alpha) mod n */
  bn.mov    w24, w0
  bn.mov    w25, w1
  bn.mov    w26, w4
  jal       x1, mod_mul_320x128
  bn.mov    w0, w19

  /* w19 <= ([w2,w3] * w26) mod n = (k1 * alpha) mod n */
  bn.mov    w24, w2
  bn.mov    w25, w3
  jal       x1, mod_mul_320x128

  /* w0 <= (w0+w19) mod n = (k * alpha) mod n */
  bn.addm   w0, w0, w19

  /* w1 <= w0^-1 mod n = (k * alpha)^-1 mod n */
  jal       x1, mod_inv

  /* Store result. */
  li        x2, 1
  la        x3, kalpha_inv
  bn.sid    x2, 0(x3)

  /* Load masking parameter to w0 (for simulator testing). */
  la        x3, alpha
  bn.lid    x0, 0(x3)

.data

/*
Default data for simulator-based testing:
k (unmasked): 0x2648d0d248b70944dfd84c2f85ea5793729112e7cafa50abdf7ef8b7594fa2a1
k0: 0x7e8bb020f9bb74012c8d5cd1c0fe2d66bead5ed1210904c73a27d1b2cdf7c706d47c4a892130fb63
k1: 0x81744fde06448bfff9bb740087b8dbddde11e80c0bf8f1512c230bf7f965aef60b02ae2e381ea73e
modulus (p256 curve order): 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

Expected result (kalpha_inv*alpha) mod n:
0x5dd1c65fc4eae6c1ec40027ef8a50479ab0ea16d84293f99bb401f0caac1e32b
*/

.balign 32
.globl k0
k0:
.word 0x2130fb63
.word 0xd47c4a89
.word 0xcdf7c706
.word 0x3a27d1b2
.word 0x210904c7
.word 0xbead5ed1
.word 0xc0fe2d66
.word 0x2c8d5cd1
.word 0xf9bb7401
.word 0x7e8bb020

.balign 32
.globl k1
k1:
.word 0x381ea73e
.word 0x0b02ae2e
.word 0xf965aef6
.word 0x2c230bf7
.word 0x0bf8f151
.word 0xde11e80c
.word 0x87b8dbdd
.word 0xf9bb7400
.word 0x06448bff
.word 0x81744fde

/* Output: (k*alpha)^-1 mod n (256 bits). */
.balign 32
.globl kalpha_inv
kalpha_inv:
.zero 32

/* Output: Masking parameter alpha (128 bits). */
.balign 32
.globl alpha
alpha:
.zero 32
