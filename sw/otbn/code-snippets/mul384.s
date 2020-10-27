/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* 384-bit multiply example. Loads two 384-bit words from DMem (they are 512-bit
   aligned with the top 128 bits filled with 0) into w1, w0 and w3, w2 (upper
   128-bits in higher register number). Multiplies usings BN.MULQACC with the
   result placed into w6, w5, w4 (higher register numbers are higher bits). */

.section .text

# Load operands into WDRs
li x2, 0
li x3, 1
li x4, 2
li x5, 3
li x6, 32
li x7, 64
li x8, 96

bn.lid x2, 0(x0)
bn.lid x3, 0(x6)
bn.lid x4, 0(x7)
bn.lid x5, 0(x8)

/* Perform the multiply, limbs are 64-bit. Each instance of `mulqacc` will
   operate on two limbs as a 64-bit multiply produces a 128-bit result. */

/* limbs 0 & 1 */
bn.mulqacc.Z        w0.0, w2.0, 0

/* limbs 1 & 2 */
bn.mulqacc          w0.0, w2.1, 64
bn.mulqacc.so w4.L, w0.1, w2.0, 64

/* limbs 2 & 3 */
bn.mulqacc          w0.0, w2.2, 0
bn.mulqacc          w0.1, w2.1, 0
bn.mulqacc          w0.2, w2.0, 0

/* limbs 3 & 4 */
bn.mulqacc          w0.0, w2.3, 64
bn.mulqacc          w0.1, w2.2, 64
bn.mulqacc          w0.2, w2.1, 64
bn.mulqacc.so w4.U, w0.3, w2.0, 64

/* limbs 4 & 5 */
bn.mulqacc          w0.0, w3.0, 0
bn.mulqacc          w0.1, w2.3, 0
bn.mulqacc          w0.2, w2.2, 0
bn.mulqacc          w0.3, w2.1, 0
bn.mulqacc          w1.0, w2.0, 0

/* limbs 5 & 6 */
bn.mulqacc          w0.0, w3.1, 64
bn.mulqacc          w0.1, w3.0, 64
bn.mulqacc          w0.2, w2.3, 64
bn.mulqacc          w0.3, w2.2, 64
bn.mulqacc          w1.0, w2.1, 64
bn.mulqacc.so w5.L, w1.1, w2.0, 64

/* limbs 6 & 7 */
bn.mulqacc          w0.1, w3.1, 0
bn.mulqacc          w0.2, w3.0, 0
bn.mulqacc          w0.3, w2.3, 0
bn.mulqacc          w1.0, w2.2, 0
bn.mulqacc          w1.1, w2.1, 0

/* limbs 7 & 8 */
bn.mulqacc          w0.2, w3.1, 64
bn.mulqacc          w0.3, w3.0, 64
bn.mulqacc          w1.0, w2.3, 64
bn.mulqacc.so w5.U, w1.1, w2.2, 64

/* limbs 8 & 9 */
bn.mulqacc          w0.3, w3.1, 0
bn.mulqacc          w1.0, w3.0, 0
bn.mulqacc          w1.1, w2.3, 0

/* limbs 9 & 10 */
bn.mulqacc          w1.0, w3.1, 64
bn.mulqacc.so w6.L, w1.1, w3.0, 64

/* limbs 10 & 11 */
bn.mulqacc.so w6.U, w1.1, w3.1, 0

ecall

.section .data

/* 384-bit integer

   c0cd8ace94e3f125 d81268464fb3d215
   e24f29866623b503 c85985f8978d55f9
   046d4d30998ce236 ee39922af4dbeb77

   (.quad below is in reverse order with zero padding) */
operand1:
  .quad 0xee39922af4dbeb77
  .quad 0x046d4d30998ce236
  .quad 0xc85985f8978d55f9
  .quad 0xe24f29866623b503
  .quad 0xd81268464fb3d215
  .quad 0xc0cd8ace94e3f125
  .quad 0x0
  .quad 0x0

/* 384-bit integer

   ae136ecc5716e8fe b65912b2b0fbc581
   92cb9b695f0bfde3 0aba0b31d86c1918
   babbd37fe428bf65 3d6d6b978170b74a

   (.quad below is in reverse order with zero padding) */
operand2:
  .quad 0x3d6d6b978170b74a
  .quad 0xbabbd37fe428bf65
  .quad 0x0aba0b31d86c1918
  .quad 0x92cb9b695f0bfde3
  .quad 0xb65912b2b0fbc581
  .quad 0xae136ecc5716e8fe
  .quad 0x0
  .quad 0x0

/* Expected result is
   w6 =
   831a570bed8e76bb 735861e7a8e39c4c
   56f945cface6d78d 2f108731983b998d

   w5 =
   ccd29b3148fbe3ae 40187a515f2524c2
   70b911a08ae0e4ac d6a0c633bad59cab

   w4 =
   c02f9f7c1521e937 31d623426dbfa830
   c4df807f413b6763 921c8782f7f42166 */

