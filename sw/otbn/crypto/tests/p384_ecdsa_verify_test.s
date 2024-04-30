/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 ECDSA signature verification
 *
 * Runs the P-384 ECDSA signature verification algorithm for message, nonce
 * and private key contained in the .data section below.
 *
 * See comment at the end of the file for expected values of result.
 */

.section .text.start

p384_ecdsa_verify_test:
  /* call ECDSA signature verification subroutine in P-384 lib */
  jal      x1, p384_verify

  /* load signature to wregs for comparison with reference */
  li        x2, 0
  la        x3, rnd
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall


.data

/* message */
.globl msg
msg:
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .zero 16

/* signature R */
.globl r
r:
  .word 0xb68c28d8
  .word 0x2b23ce3a
  .word 0x9a1a30fc
  .word 0x56e186cf
  .word 0x12d35b38
  .word 0xc16c09de
  .word 0x0235d77e
  .word 0x49d29eef
  .word 0xd3c43053
  .word 0xb45990db
  .word 0x7c0d8125
  .word 0xb2fcf95c
  .zero 16

/* signature S */
.globl s
s:
  .word 0x24bc1bf9
  .word 0x752042f5
  .word 0x98144c27
  .word 0x77e415a1
  .word 0xa78101eb
  .word 0x0016f9c3
  .word 0x3e7f6895
  .word 0x80eb391d
  .word 0xf19a653d
  .word 0xfa9554e0
  .word 0xe34d88c1
  .word 0x1a72ebdd
  .zero 16

/* public key x-coordinate */
.globl x
x:
  .word 0x4877f3d1
  .word 0x7b829460
  .word 0xb1cac609
  .word 0x5869de54
  .word 0xee0e2beb
  .word 0x6c30f2d8
  .word 0x47e80661
  .word 0x394d8b70
  .word 0xcf60d89e
  .word 0x1a9ea916
  .word 0xb439d701
  .word 0xca230836
  .zero 16

/* public key y-coordinate */
.globl y
y:
  .word 0xc181f90f
  .word 0xc31ef079
  .word 0xbf3aff6e
  .word 0xc7e55880
  .word 0xec18818c
  .word 0xcea028a9
  .word 0x928c3e92
  .word 0x82b63bf3
  .word 0xd65e905d
  .word 0x68eef2d1
  .word 0x03afe2c2
  .word 0xaaafcad2
  .zero 16

/* signature verification result x_res (rnd) */
.globl rnd
rnd:
  .zero 64
