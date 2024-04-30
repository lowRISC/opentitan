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

  li    x3, 1
  beq   x2, x3, p384_ecdsa_sign

  li    x3, 2
  beq   x2, x3, p384_ecdsa_verify

  /* Mode is neither 1 (= sign) nor 2 (= verify). Fail. */
  unimp

.text
p384_ecdsa_sign:
  jal      x1, p384_sign
  ecall

p384_ecdsa_verify:
  /*jal      x1, p384_verify*/
  ecall

.data

/* Freely available DMEM space. */

/* Operation mode (1 = sign; 2 = verify) */
.globl mode
.balign 4
mode:
  .zero 4

/* All constants below must be 256b-aligned. */

/* random scalar k0*/
.global k0
.balign 64
k0:
  .zero 64

/* random scalar k1*/
.globl k1
.balign 64
k1:
  .zero 64

/* randomness for blinding */
.globl rnd
.balign 64
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

/* private key d0 */
.globl d0
.balign 64
d0:
  .zero 64

/* private key d1 */
.globl d1
.balign 64
d1:
  .zero 64

/* verification result x_r (aka x_1) */
.globl x_r
.balign 64
x_r:
  .zero 64
