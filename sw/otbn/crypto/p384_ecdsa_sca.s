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
  jal      x1, p384_ecdsa_setup
  jal      x1, p384_sign
  ecall

p384_ecdsa_verify:
  /*jal      x1, p384_verify*/
  ecall

/**
 * Populate the variables rnd and k with randomness, and setup data pointers.
 */
p384_ecdsa_setup:
  /* Point dptr_k0 to k0. */
  la        x10, k0
  la        x11, dptr_k0
  sw        x10, 0(x11)

  /* Point dptr_k1 to k1. */
  la        x10, k1
  la        x11, dptr_k1
  sw        x10, 0(x11)

  /* Point dptr_d0 to d0. */
  la        x10, d0
  la        x11, dptr_d0
  sw        x10, 0(x11)

  /* Point dptr_d1 to d1. */
  la        x10, d1
  la        x11, dptr_d1
  sw        x10, 0(x11)

  /* Point dptr_msg to msg. */
  la        x10, msg
  la        x11, dptr_msg
  sw        x10, 0(x11)

  /* Point dptr_r to sig_r. */
  la        x10, r
  la        x11, dptr_r
  sw        x10, 0(x11)

  /* Point dptr_s to sig_s. */
  la        x10, s
  la        x11, dptr_s
  sw        x10, 0(x11)

  ret

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
.global k1
.balign 64
k1:
  .zero 64

/* randomness for blinding */
.global rnd
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

/* pointer to rnd (dptr_rnd) */
.globl dptr_rnd
dptr_rnd:
  .zero 4

/* pointer to k0 (dptr_k0) */
.globl dptr_k0
dptr_k0:
  .zero 4

/* pointer to k1 (dptr_k1) */
.globl dptr_k1
dptr_k1:
  .zero 4

/* pointer to msg (dptr_msg) */
.globl dptr_msg
dptr_msg:
  .zero 4

/* pointer to R (dptr_r) */
.globl dptr_r
dptr_r:
  .zero 4

/* pointer to S (dptr_s) */
.globl dptr_s
dptr_s:
  .zero 4

/* pointer to X (dptr_x) */
.globl dptr_x
dptr_x:
  .zero 4

/* pointer to Y (dptr_y) */
.globl dptr_y
dptr_y:
  .zero 4

/* pointer to d0 (dptr_d0) */
.globl dptr_d0
dptr_d0:
  .zero 4

/* pointer to d1 (dptr_d1) */
.globl dptr_d1
dptr_d1:
  .zero 4
