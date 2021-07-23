/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Elliptic curve P-256 ECDSA
 *
 * Uses OTBN ECC P-256 lib to perform an ECDSA operations.
 */

.text

.globl p256_ecdsa_sign
p256_ecdsa_sign:
  jal      x1, p256_sign
  ecall

.globl p256_ecdsa_verify
p256_ecdsa_verify:
  jal      x1, p256_verify
  ecall


.data

/* Freely available DMEM space. */
/* All constants below must be 256b-aligned. */

/* random scalar k */
.globl k
.balign 32
k:
  .zero 32

/* randomness for blinding */
.globl rnd
.balign 32
rnd:
  .zero 32

/* message digest */
.globl msg
.balign 32
msg:
  .zero 32

/* signature R */
.globl r
.balign 32
r:
  .zero 32

/* signature S */
.globl s
.balign 32
s:
  .zero 32

/* public key x-coordinate */
.globl x
.balign 32
x:
  .zero 32

/* public key y-coordinate */
.globl y
.balign 32
y:
  .zero 32

/* private key d */
.globl d
.balign 32
d:
  .zero 32

/* verification result x_r (aka x_1) */
.globl x_r
.balign 32
x_r:
  .zero 32
