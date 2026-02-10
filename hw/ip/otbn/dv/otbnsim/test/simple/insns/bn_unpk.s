/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
/*
  Load the vectors
*/
addi x2, x0, 0

la     x3,   vec1
bn.lid x2++, 0(x3)
la     x3,   vec2
bn.lid x2++, 0(x3)
la     x3,   vec3
bn.lid x2++, 0(x3)

/* Unpack the vectors */
bn.unpk w10, w1, w0, 0
bn.unpk w11, w1, w0, 192
bn.unpk w12, w2, w1, 128
bn.unpk w13, w2, w2, 64

ecall

.section .data
/*
  Vectors to unpack 24-bit elements from
  WDR0, Bytes  0-23: Vector A (each element is CCDDEE)
  WDR0, Bytes 24-31: 1st part of vector B (each element is AABBAA)
  WDR1, Bytes  0-15: 2nd part of vector B
  WDR1, Bytes 16-31: 1st part of vector C (each element is 33FF33)
  WDR2, Bytes  0- 7: 2nd part of vector C
  WDR2, Bytes  8-31: Vector D (each element is 775577)

  WDR0 = 0xBBAA_AABBAA_AABBAA_CCDDEE_CCDDEE_CCDDEE_CCDDEE_CCDDEE_CCDDEE_CCDDEE_CCDDEE
         0xBBAAAABBAAAABBAACCDDEECCDDEECCDDEECCDDEECCDDEECCDDEECCDDEECCDDEE
  WDR1 = 0x33_33FF33_33FF33_33FF33_33FF33_33FF33_AABBAA_AABBAA_AABBAA_AABBAA_AABBAA_AA
         0x3333FF3333FF3333FF3333FF3333FF33AABBAAAABBAAAABBAAAABBAAAABBAAAA
  WDR2 = 0x775577_775577_775577_775577_775577_775577_775577_775577_33FF33_33FF33_33FF
         0x77557777557777557777557777557777557777557777557733FF3333FF3333FF

  Expected results
  VecA = 0x00CCDDEE_00CCDDEE_00CCDDEE_00CCDDEE_00CCDDEE_00CCDDEE_00CCDDEE_00CCDDEE
  VecB = 0x00AABBAA_00AABBAA_00AABBAA_00AABBAA_00AABBAA_00AABBAA_00AABBAA_00AABBAA
  VecC = 0x0033FF33_0033FF33_0033FF33_0033FF33_0033FF33_0033FF33_0033FF33_0033FF33
  VecD = 0x00775577_00775577_00775577_00775577_00775577_00775577_00775577_00775577
*/
vec1:
  .word 0xEECCDDEE
  .word 0xDDEECCDD
  .word 0xCCDDEECC
  .word 0xEECCDDEE
  .word 0xDDEECCDD
  .word 0xCCDDEECC
  .word 0xAAAABBAA
  .word 0xBBAAAABB

vec2:
  .word 0xAABBAAAA
  .word 0xAAAABBAA
  .word 0xBBAAAABB
  .word 0xAABBAAAA
  .word 0x3333FF33
  .word 0xFF3333FF
  .word 0x33FF3333
  .word 0x3333FF33

vec3:
  .word 0xFF3333FF
  .word 0x33FF3333
  .word 0x77775577
  .word 0x55777755
  .word 0x77557777
  .word 0x77775577
  .word 0x55777755
  .word 0x77557777
