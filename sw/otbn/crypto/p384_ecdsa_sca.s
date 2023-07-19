/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Elliptic curve P-384 ECDSA
 *
 * Uses OTBN ECC P-384 lib to perform an ECDSA operations.
 */

.section .text.start
.globl start
start:
  /* Read mode, then tail-call either p384_ecdsa_sign or p384_ecdsa_verify */
  la    x2, mode
  lw    x2, 0(x2)

  /* Copy d to d0 in dmem (d1 is zero) */
  la        x10, d
  la        x2, d0
  li        x3, 1
  bn.lid    x3++, 0(x10)
  bn.lid    x3++, 32(x10)
  li        x3, 1
  bn.sid    x3++, 0(x2)
  bn.sid    x3++, 32(x2)

  /* Point dptr_d0 to d0 and dptr_d1 to d1. */
  la        x11, dptr_d0
  la        x2, d0
  sw        x2, 0(x11)
  la        x11, dptr_d1
  la        x2, d1
  sw        x2, 0(x11)

  li    x3, 1
  beq   x2, x3, p384_ecdsa_sign

  li    x3, 2
  beq   x2, x3, p384_ecdsa_verify

  /* Mode is neither 1 (= sign) nor 2 (= verify). Fail. */
  unimp

.text
p384_ecdsa_sign:
  jal      x1, p384_ecdsa_setup_rand
  jal      x1, p384_sign
  ecall

p384_ecdsa_verify:
  /*jal      x1, p384_verify*/
  ecall

/**
 * Populate the variables rnd and k with randomness, and setup data pointers.
 */
p384_ecdsa_setup_rand:
  /* Obtain the blinding constant from URND, and write it to `rnd` in DMEM. */
  /* bn.wsrr   w0, 0x2 */ /* URND */
  la        x10, rnd
  /* bn.sid    x0, 0(x10) */

  /* Copy rnd to k1 in dmem */
  la        x2, k1
  li        x3, 1
  bn.lid    x3++, 0(x10)
  bn.lid    x3++, 32(x10)
  li        x3, 1
  bn.sid    x3++, 0(x2)
  bn.sid    x3++, 32(x2)

  /* Point dptr_k1 to k1. */
  la        x11, dptr_k1
  sw        x2, 0(x11)

  /* Obtain the nonce (k) from RND. */
  /*bn.wsrr   w0, 0x1 *//* RND */
  la        x10, k
  /*bn.sid    x0, 0(x10)*/

  /* Copy k to k0 in dmem */
  la        x2, k0
  li        x3, 1
  bn.lid    x3++, 0(x10)
  bn.lid    x3++, 32(x10)
  li        x3, 1
  bn.sid    x3++, 0(x2)
  bn.sid    x3++, 32(x2)

  /* Point dptr_k0 to k0. */
  la        x11, dptr_k0
  sw        x2, 0(x11)

  ret

.data

/* Freely available DMEM space. */

/* Operation mode (1 = sign; 2 = verify) */
.globl mode
.balign 4
mode:
  .zero 4

/* All constants below must be 256b-aligned. */

/* random scalar k */
.global k
.balign 64
k:
  .zero 64

/* 1st scalar share k0 (448-bit) */
.balign 64
k0:
  .zero 64

/* 2nd scalar share k1 (448-bit) */
.balign 64
k1:
  .zero 64

/* randomness for blinding */
.balign 64
.global rnd
rnd:
  .zero 64

/* message digest */
.globl msg
.balign 64
msg:
  .zero 64

/* signature R */
.globl r
.balign 64
r:
  .zero 64

/* signature S */
.globl s
.balign 64
s:
  .zero 64

/* public key x-coordinate */
.globl x
.balign 64
x:
  .zero 64

/* public key y-coordinate */
.globl y
.balign 64
y:
  .zero 64

/* private key d */
.globl d
.balign 64
d:
  .zero 64

/* 1st private key share d0 (448-bit) */
.balign 64
d0:
  .zero 64

/* 2nd private key share d1 (448-bit) */
.balign 64
d1:
  .zero 64

/* verification result x_r (aka x_1) */
.globl x_r
.balign 64
x_r:
  .zero 64

/* pointer to k (dptr_k) */
.globl dptr_k
dptr_k:
  .zero 4

/* pointer to rnd (dptr_rnd) */
.globl dptr_rnd
dptr_rnd:
  .zero 4

/* pointer to d (dptr_d) */
.globl dptr_d
dptr_d:
  .zero 4
