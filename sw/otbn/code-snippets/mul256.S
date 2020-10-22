/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* 256-bit multiply example. Loads two 256-bit words from DMem into w1, w0.
   Multiplies usings BN.MULQACC with the result placed into w3, w2 (upper half
   in w3). */

.section .text

/* Load operands into WDRs */
li x2, 0
li x3, 1
li x4, 32

bn.lid x2, 0(x0)
bn.lid x3, 0(x4)

/* Perform the multiply, limbs are 64-bit. Each instance of `mulqacc` will
   operate on two limbs as a 64-bit multiply produces a 128-bit result. */

/* limbs 0 & 1 */
bn.mulqacc.Z        w0.0, w1.0, 0

/* limbs 1 & 2 */
bn.mulqacc          w0.1, w1.0, 64
bn.mulqacc.so w2.L, w0.0, w1.1, 64

/* limbs 2 & 3 */
bn.mulqacc          w0.2, w1.0, 0
bn.mulqacc          w0.1, w1.1, 0
bn.mulqacc          w0.0, w1.2, 0

/* limbs 3 & 4 */
bn.mulqacc          w0.3, w1.0, 64
bn.mulqacc          w0.2, w1.1, 64
bn.mulqacc          w0.1, w1.2, 64
bn.mulqacc.so w2.U, w0.0, w1.3, 64

/* limbs 4 & 5 */
bn.mulqacc          w0.3, w1.1, 0
bn.mulqacc          w0.2, w1.2, 0
bn.mulqacc          w0.1, w1.3, 0

/* limbs 5 & 6 */
bn.mulqacc          w0.3, w1.2, 64
bn.mulqacc.so w3.L, w0.2, w1.3, 64

/* limbs 6 & 7 */
bn.mulqacc.so w3.U, w0.3, w1.3, 0

ecall

.section .data

/* 256-bit integer

   fbc20c8e4ba684f2 f6835831c3623f41
   49de6d75d0221f41 61a5a8d66985591e

   (.quad below is in reverse order) */

operand1:
  .quad 0x61a5a8d66985591e
  .quad 0x49de6d75d0221f41
  .quad 0xf6835831c3623f41
  .quad 0xfbc20c8e4ba684f2

/* 256-bit integer

   10ad673384d81d98 1a1c98e116948392
   60f39da06db956ec 5de6ee4dbd0f089d

   (.quad below is in reverse order) */

operand2:
   .quad 0x5de6ee4dbd0f089d
   .quad 0x60f39da06db956ec
   .quad 0x1a1c98e116948392
   .quad 0x10ad673384d81d98

/* Expected result is
   w3 =
   1066a8691e3ddfee a0a622d04cfd63b4
   ea93fcc837b795eb 3f2b811bfa6dc7f2

   w2 =
   dad4a618536bfd33 565eff3285ab75a5
   59b7199e0622d5ee ed40926c40529766 */
