/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
/*
  Load the vectors
*/
addi x2, x0, 0

la     x3,   vecA
bn.lid x2++, 0(x3)
la     x3,   vecB
bn.lid x2++, 0(x3)
la     x3,   vecC
bn.lid x2++, 0(x3)
la     x3,   vecD
bn.lid x2++, 0(x3)

/* Pack the vectors */
bn.pack w10, w1, w0, 64
bn.pack w11, w2, w1, 128
bn.pack w12, w3, w2, 192

ecall

.section .data
/*
  Vectors to pack to 24-bit elements (FE byte should be ignored)
  VecA = 0xFECCDDEE_FECCDDEE_FECCDDEE_FECCDDEE_FECCDDEE_FECCDDEE_FECCDDEE_FECCDDEE
  VecB = 0xFEAABBAA_FEAABBAA_FEAABBAA_FEAABBAA_FEAABBAA_FEAABBAA_FEAABBAA_FEAABBAA
  VecC = 0xFE33FF33_FE33FF33_FE33FF33_FE33FF33_FE33FF33_FE33FF33_FE33FF33_FE33FF33
  VecD = 0xFE775577_FE775577_FE775577_FE775577_FE775577_FE775577_FE775577_FE775577

  WDR0, Bytes  0-23: Vector A (each element is CCDDEE)
  WDR0, Bytes 24-31: 1st part of vector B (each element is AABBAA)
  WDR1, Bytes  0-15: 2nd part of vector B
  WDR1, Bytes 16-31: 1st part of vector C (each element is 33FF33)
  WDR2, Bytes  0- 7: 2nd part of vector C
  WDR2, Bytes  8-31: Vector D (each element is 775577)

  Expected results
  WDR0 = 0xBBAA_AABBAA_AABBAA_CCDDEE_CCDDEE_CCDDEE_CCDDEE_CCDDEE_CCDDEE_CCDDEE_CCDDEE
         0xBBAAAABBAAAABBAACCDDEECCDDEECCDDEECCDDEECCDDEECCDDEECCDDEECCDDEE
  WDR1 = 0x33_33FF33_33FF33_33FF33_33FF33_33FF33_AABBAA_AABBAA_AABBAA_AABBAA_AABBAA_AA
         0x3333FF3333FF3333FF3333FF3333FF33AABBAAAABBAAAABBAAAABBAAAABBAAAA
  WDR2 = 0x775577_775577_775577_775577_775577_775577_775577_775577_33FF33_33FF33_33FF
         0x77557777557777557777557777557777557777557777557733FF3333FF3333FF
*/
vecA:
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE

vecB:
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA

vecC:
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33

vecD:
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
