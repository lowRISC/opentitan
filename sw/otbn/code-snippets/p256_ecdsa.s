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
  jal      x1, p256_init
  jal      x1, p256_sign
  ecall

.globl p256_ecdsa_verify
p256_ecdsa_verify:
  jal      x1, p256_init
  jal      x1, p256_verify
  ecall


.data

/*
The structure of the 256b below are mandated by the calling convention of the
P-256 ECDSA library.
*/

/* pointer to k */
.globl dptr_k
dptr_k:
  .word k

/* pointer to rnd */
.globl dptr_rnd
dptr_rnd:
  .word rnd

/* pointer to msg */
.globl dptr_msg
dptr_msg:
  .word msg

/* pointer to R */
.globl dptr_r
dptr_r:
  .word r

/* pointer to S */
.globl dptr_s
dptr_s:
  .word s

/* pointer to X */
.globl dptr_x
dptr_x:
  .word x

/* pointer to Y */
.globl dptr_y
dptr_y:
  .word y

/* pointer to D */
.globl dptr_d
dptr_d:
  .word d

/* Freely available DMEM space. */
/* All constants below must be 256b-aligned. */

/* random scalar k */
.globl k
.balign 32
k:
  .zero 32

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
