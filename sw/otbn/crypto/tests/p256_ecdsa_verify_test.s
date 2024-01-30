/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 ECDSA signature verification test
 *
 * Uses OTBN ECC P-256 lib to perform an ECDSA signature verification.
 * Coordinates of the public key, the message digest and R and S of the
 * signature are provided in the .data section below.
 *
 * The signature verification was successful if the return value in x_r and R
 * are identical.
 */

.section .text.start

ecdsa_verify_test:

  /* call ECDSA signature verification subroutine in P-256 lib */
  jal      x1, p256_verify

  /* load results to wregs for comparison with reference */
  li        x2, 0
  la        x3, x_r
  bn.lid    x2, 0(x3)
  la        x3, ok
  lw        x2, 0(x3)

  ecall


.data

.globl msg
.balign 32
msg:
  .word 0x4456fd21
  .word 0x400bdd7d
  .word 0xb54d7452
  .word 0x17d015f1
  .word 0x90d4d90b
  .word 0xb028ad8a
  .word 0x6ce90fef
  .word 0x06d71207

/* signature R */
.globl r
.balign 32
r:
  .word 0x80a9674a
  .word 0x1147ea56
  .word 0x0c7d87dd
  .word 0x99504edd
  .word 0xbe064de2
  .word 0x6b35843c
  .word 0x7dd27f33
  .word 0x815215ad

/* signature S */
.globl s
.balign 32
s:
  .word 0xc93fd605
  .word 0xd0b1051e
  .word 0xe90a6d17
  .word 0x4dad9404
  .word 0x99e589ad
  .word 0x86e30cd9
  .word 0xc4440420
  .word 0xa3991e01

/* public key x-coordinate */
.globl x
.balign 32
x:
  .word 0xbfa8c334
  .word 0x9773b7b3
  .word 0xf36b0689
  .word 0x6ec0c0b2
  .word 0xdb6c8bf3
  .word 0x1628ce58
  .word 0xfacdc546
  .word 0xb5511a6a

/* public key y-coordinate */
.globl y
.balign 32
y:
  .word 0x9e008c2e
  .word 0xa8707058
  .word 0xab9c6924
  .word 0x7f7a11d0
  .word 0xb53a17fa
  .word 0x43dd09ea
  .word 0x1f31c143
  .word 0x42a1c697

/* signature verification result x_r */
.globl x_r
.balign 32
x_r:
  .zero 32
