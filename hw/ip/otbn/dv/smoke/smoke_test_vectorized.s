/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


# OTBN smoke test vectorized runs various vectorized instructions which are expected to produce the
# final register state defined in smoke_vectorized_expected.txt

.section .text.start
/***********
 * BN.ADDV *
 ***********/
addi   x2,   x0, 2
la     x3,   vec32a_bnaddv
bn.lid x2++, 0(x3)
la     x3,   vec32b_bnaddv
bn.lid x2++, 0(x3)

bn.addv.8s w10, w2, w3

/************
 * BN.ADDVM *
 ************/
addi   x2,   x0, 2
la     x3,   vec32a0_bnaddvm
bn.lid x2++, 0(x3)
la     x3,   vec32b0_bnaddvm
bn.lid x2++, 0(x3)

li           x2,  20
la           x3,  mod32
bn.lid       x2,  0(x3)
bn.wsrw      MOD, w20

bn.addvm.8s  w11, w2, w3

/**********
 * BN.SHV *
 **********/
addi   x2, x0, 0
la     x3, vecorig_bnshv
bn.lid x2, 0(x3)

bn.shv.8s  w12, w0 << 11
bn.shv.8s  w13, w0 >> 30

/***********
 * BN.SUBV *
 ***********/
addi   x2,   x0, 2
la     x3,   vec32a0_bnsubv
bn.lid x2++, 0(x3)
la     x3,   vec32b0_bnsubv
bn.lid x2++, 0(x3)

bn.subv.8s  w14, w2, w3

/************
 * BN.SUBVM *
 ************/
addi   x2,   x0, 2
la     x3,   vec32a0_bnsubvm
bn.lid x2++, 0(x3)
la     x3,   vec32b0_bnsubvm
bn.lid x2++, 0(x3)

li           x2,  20
la           x3,  mod32
bn.lid       x2,  0(x3)
bn.wsrw      MOD, w20
bn.subvm.8s  w15, w2, w3

/***********
 * BN.TRN1 *
 ***********/
addi   x2,   x0, 2
la     x3,   vec32a_bntrn1
bn.lid x2++, 0(x3)
la     x3,   vec32b_bntrn1
bn.lid x2++, 0(x3)

bn.trn1.8s w16, w2, w3

/***********
 * BN.TRN2 *
 ***********/
addi   x2,   x0, 2
la     x3,   vec32a_bntrn2
bn.lid x2++, 0(x3)
la     x3,   vec32b_bntrn2
bn.lid x2++, 0(x3)

bn.trn2.8s w17, w2, w3

/************************
 * BN.MULV and BN.MULVL *
 ************************/
addi   x2,   x0, 2
la     x3,   vec32a0_bnmulv
bn.lid x2++, 0(x3)
la     x3,   vec32b0_bnmulv
bn.lid x2++, 0(x3)

bn.mulv.8s   w18, w2, w3
bn.mulvl.8s  w19, w2, w3, 7

/************
 * BN.MULVM *
 ************/
addi   x2,   x0, 2
la     x3,   vec32a0_bnmulvm
bn.lid x2++, 0(x3)
la     x3,   vec32b0_bnmulvm
bn.lid x2++, 0(x3)

/* Load the modulus into w20 and then into MOD*/
li           x2,  20
la           x3,  mod32_bnmulvm
bn.lid       x2,  0(x3)
bn.wsrw      MOD, w20
bn.mulvm.8s  w21, w2, w3

/*************
 * BN.MULVML *
 *************/
addi   x2,   x0, 2
la     x3,   vec32a_bnmulvml
bn.lid x2++, 0(x3)
la     x3,   vec32b_bnmulvml
bn.lid x2++, 0(x3)

/* Load the modulus into w20 and then into MOD*/
addi    x2,  x0, 20
la      x3,  mod32_bnmulvml
bn.lid  x2,  0(x3)
bn.wsrw MOD, w20

bn.mulvml.8s  w22, w2, w3, 7

/***********
 * BN.PACK *
 ***********/
addi   x2,   x0, 0
la     x3,   vecA_bnpack
bn.lid x2++, 0(x3)
la     x3,   vecB_bnpack
bn.lid x2++, 0(x3)
la     x3,   vecC_bnpack
bn.lid x2++, 0(x3)
la     x3,   vecD_bnpack
bn.lid x2++, 0(x3)

bn.pack w23, w1, w0, 64
bn.pack w24, w2, w1, 128
bn.pack w25, w3, w2, 192

/***********
 * BN.UNPK *
 ***********/
addi   x2,   x0, 0
la     x3,   vec1_bnunpk
bn.lid x2++, 0(x3)
la     x3,   vec2_bnunpk
bn.lid x2++, 0(x3)
la     x3,   vec3_bnunpk
bn.lid x2++, 0(x3)

bn.unpk w26, w1, w0, 0
bn.unpk w27, w1, w0, 192
bn.unpk w28, w2, w1, 128
bn.unpk w29, w2, w2, 64

addi x2, x0, 0 /* clear x2 as otherwise WDR index is there */
addi x3, x0, 0 /* clear x3 as otherwise an address is there */

/* Clear working WDRs */
bn.xor w0, w0, w0
bn.xor w1, w1, w1
bn.xor w2, w2, w2
bn.xor w3, w3, w3

ecall

.section .data
/* These vectors can be generated using ../otbnsim/test/generate_bn_simd_tests.py */

/*
  32bit vector vec32a for instruction addv
  vec32a = [-2147483648 -2147483648  2147483647  2147483647  2147483647 -2147483648
 -2147483648  2147483647]
  vec32a = 0x80000000800000007fffffff7fffffff7fffffff80000000800000007fffffff
*/
vec32a_bnaddv:
  .word 0x7fffffff
  .word 0x80000000
  .word 0x80000000
  .word 0x7fffffff
  .word 0x7fffffff
  .word 0x7fffffff
  .word 0x80000000
  .word 0x80000000

/*
  32bit vector vec32b for instruction addv
  vec32b = [-32  -1  32   1   1  -1  -1   1]
  vec32b = 0xffffffe0ffffffff000000200000000100000001ffffffffffffffff00000001
*/
vec32b_bnaddv:
  .word 0x00000001
  .word 0xffffffff
  .word 0xffffffff
  .word 0x00000001
  .word 0x00000001
  .word 0x00000020
  .word 0xffffffff
  .word 0xffffffe0

/*
  Result of 32bit addv
  res = [2147483616, 2147483647, -2147483617, -2147483648, -2147483648, 2147483647, 2147483647, -2147483648]
  res = 0x7fffffe07fffffff8000001f80000000800000007fffffff7fffffff80000000
*/

/*
  32bit vector mod32 for instruction addvm
  mod32 = [8380417]
  mod32 = 0x00000000000000000000000000000000000000000000000000000000007fe001
*/
mod32:
  .word 0x007fe001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/*
  32bit vector vec32a0 for instruction addvm
  vec32a0 = [4294967295, 4294967295, 4190208, 8380416, 4294967295, 0, 4190208, 8380416]
  vec32a0 = 0xffffffffffffffff003ff000007fe000ffffffff00000000003ff000007fe000
*/
vec32a0_bnaddvm:
  .word 0x007fe000
  .word 0x003ff000
  .word 0x00000000
  .word 0xffffffff
  .word 0x007fe000
  .word 0x003ff000
  .word 0xffffffff
  .word 0xffffffff

/*
  32bit vector vec32b0 for instruction addvm
  vec32b0 = [2024, 1, 2793472, 8380414, 2024, 2147483647, 2793472, 8380414]
  vec32b0 = 0x000007e800000001002aa000007fdffe000007e87fffffff002aa000007fdffe
*/
vec32b0_bnaddvm:
  .word 0x007fdffe
  .word 0x002aa000
  .word 0x7fffffff
  .word 0x000007e8
  .word 0x007fdffe
  .word 0x002aa000
  .word 0x00000001
  .word 0x000007e8

/*
  Result of 32bit addvm
  res = [4286588902, 4286586879, 6983680, 8380413, 4286588902, 2139103230, 6983680, 8380413]
  res = 0xff8027e6ff801fff006a9000007fdffdff8027e67f801ffe006a9000007fdffd
*/

/*
  vector for instruction shv
  vec16orig = n/a
  vec16orig = 0x9397271b502c41d6cf2538cfa72bf6800d250f06252fff02a626711a3a60e2eb
*/
vecorig_bnshv:
  .word 0x3a60e2eb
  .word 0xa626711a
  .word 0x252fff02
  .word 0x0d250f06
  .word 0xa72bf680
  .word 0xcf2538cf
  .word 0x502c41d6
  .word 0x9397271b

/*
  Result of 32bit shv left (res = [bitshift in decimals])
  res = [11]
  res = 0xb938d800620eb00029c678005fb40000287830007ff810003388d00007175800
*/
/*
  Result of 32bit shv right (res = [bitshift in decimals])
  res = [30]
  res = 0x0000000200000001000000030000000200000000000000000000000200000000
*/

/*
  32bit vector vec32a0 for instruction subv
  vec32a0 = [0, 0, 2147483647, 2147483647, 0, 4294967295, 1684, 0]
  vec32a0 = 0x00000000000000007fffffff7fffffff00000000ffffffff0000069400000000
*/
vec32a0_bnsubv:
  .word 0x00000000
  .word 0x00000694
  .word 0xffffffff
  .word 0x00000000
  .word 0x7fffffff
  .word 0x7fffffff
  .word 0x00000000
  .word 0x00000000

/*
  32bit vector vec32b0 for instruction subv
  vec32b0 = [2048, 1, 2147483647, 0, 2048, 1, 437, 1]
  vec32b0 = 0x00000800000000017fffffff000000000000080000000001000001b500000001
*/
vec32b0_bnsubv:
  .word 0x00000001
  .word 0x000001b5
  .word 0x00000001
  .word 0x00000800
  .word 0x00000000
  .word 0x7fffffff
  .word 0x00000001
  .word 0x00000800

/*
  Result of 32bit subv
  res = [4294965248, 4294967295, 0, 2147483647, 4294965248, 4294967294, 1247, 4294967295]
  res = 0xfffff800ffffffff000000007ffffffffffff800fffffffe000004dfffffffff
*/

/*
  32bit vector vec32a0 for instruction subvm
  vec32a0 = [0, 0, 4190208, 8380414, 0, 4294967295, 4190208, 8380414]
  vec32a0 = 0x0000000000000000003ff000007fdffe00000000ffffffff003ff000007fdffe
*/
vec32a0_bnsubvm:
  .word 0x007fdffe
  .word 0x003ff000
  .word 0xffffffff
  .word 0x00000000
  .word 0x007fdffe
  .word 0x003ff000
  .word 0x00000000
  .word 0x00000000

/*
  32bit vector vec32b0 for instruction subvm
  vec32b0 = [2048, 1, 2793472, 8380416, 2048, 2147483647, 2793472, 8380416]
  vec32b0 = 0x0000080000000001002aa000007fe000000008007fffffff002aa000007fe000
*/
vec32b0_bnsubvm:
  .word 0x007fe000
  .word 0x002aa000
  .word 0x7fffffff
  .word 0x00000800
  .word 0x007fe000
  .word 0x002aa000
  .word 0x00000001
  .word 0x00000800

/*
  Result of 32bit subvm
  res = [8378369, 8380416, 1396736, 8380415, 8378369, 2147483648, 1396736, 8380415]
  res = 0x007fd801007fe00000155000007fdfff007fd8018000000000155000007fdfff
*/

/*
  32bit vector vec32a for instruction trn1
  vec32a = n/a
  vec32a = 0x21caff82bc486be36aaecc11ccdd1e5621164f9c456fec1611a7c626ee821bdb
*/
vec32a_bntrn1:
  .word 0xee821bdb
  .word 0x11a7c626
  .word 0x456fec16
  .word 0x21164f9c
  .word 0xccdd1e56
  .word 0x6aaecc11
  .word 0xbc486be3
  .word 0x21caff82

/*
  32bit vector vec32b for instruction trn1
  vec32b = n/a
  vec32b = 0x489bc5561f6b6e6b99c19e9f26795d6dbd9a16d9ff11c45542568d446c0130d1
*/
vec32b_bntrn1:
  .word 0x6c0130d1
  .word 0x42568d44
  .word 0xff11c455
  .word 0xbd9a16d9
  .word 0x26795d6d
  .word 0x99c19e9f
  .word 0x1f6b6e6b
  .word 0x489bc556

/*
  Result of 32bit trn1
  res = n/a
  res = 0x1f6b6e6bbc486be326795d6dccdd1e56ff11c455456fec166c0130d1ee821bdb
*/

/*
  32bit vector vec32a for instruction trn2
  vec32a = n/a
  vec32a = 0x1000000a00300008001000080090000600050008070000040500000400030002
*/
vec32a_bntrn2:
  .word 0x00030002
  .word 0x05000004
  .word 0x07000004
  .word 0x00050008
  .word 0x00900006
  .word 0x00100008
  .word 0x00300008
  .word 0x1000000a

/*
  32bit vector vec32b for instruction trn2
  vec32b = n/a
  vec32b = 0x0100a00003000080000100809000060050000800700000400050004000300020
*/
vec32b_bntrn2:
  .word 0x00300020
  .word 0x00500040
  .word 0x70000040
  .word 0x50000800
  .word 0x90000600
  .word 0x00010080
  .word 0x03000080
  .word 0x0100a000

/*
  Result of 32bit trn2
  res = n/a
  res = 0x0100a0001000000a000100800010000850000800000500080050004005000004
*/

/*
  32bit vector vec32a0 for instruction mulv
  vec32a0 = [0, 1, 44913, 9734, 23276, 65251, 13010, 40903]
  vec32a0 = 0x00000000000000010000af710000260600005aec0000fee3000032d200009fc7
*/
vec32a0_bnmulv:
  .word 0x00009fc7
  .word 0x000032d2
  .word 0x0000fee3
  .word 0x00005aec
  .word 0x00002606
  .word 0x0000af71
  .word 0x00000001
  .word 0x00000000

/*
  32bit vector vec32b0 for instruction mulv
  vec32b0 = [4140082361, 1869666356, 636760, 207841, 59661, 52504, 947, 30691]
  vec32b0 = 0xf6c4a4b96f70d8340009b75800032be10000e90d0000cd18000003b3000077e3
*/
vec32b0_bnmulv:
  .word 0x000077e3
  .word 0x000003b3
  .word 0x0000cd18
  .word 0x0000e90d
  .word 0x00032be1
  .word 0x0009b758
  .word 0x6f70d834
  .word 0xf6c4a4b9

/*
  Result of 32bit mulv
  res = [0, 1869666356, 2828998104, 2023124294, 1388669436, 3425938504, 12320470, 1255353973]
  res = 0x000000006f70d834a89f15d878966d4652c569fccc33ac4800bbfed64ad32e75
*/

/*
  Results of 32bit mulvl
  res = [0, 30691, 1378424883, 298746194, 714363716, 2002618441, 399289910, 1255353973]
  res = 0x00000000000077e35229183311ce81522a945344775d884917ccae364ad32e75
*/

/*
  32bit vector mod32 for instruction mulvm. Combined [R, q]
  mod32 = [4236238847, 8380417]
  mod32 = 0x000000000000000000000000000000000000000000000000fc7fdfff007fe001
*/
mod32_bnmulvm:
  .word 0x007fe001
  .word 0xfc7fdfff
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/*
  32bit vector vec32a0 for instruction mulvm
  vec32a0 = [140140, 2179652, 4415585, 3591344, 6089560, 5367875, 2289882, 4817594]
  vec32a0 = 0x0002236c00214244004360610036ccb0005ceb580051e8430022f0da004982ba
*/
vec32a0_bnmulvm:
  .word 0x004982ba
  .word 0x0022f0da
  .word 0x0051e843
  .word 0x005ceb58
  .word 0x0036ccb0
  .word 0x00436061
  .word 0x00214244
  .word 0x0002236c

/*
  32bit vector vec32b0 for instruction mulvm
  vec32b0 = [7268407, 3661137, 7621524, 6778366, 6274350, 2059156, 3886783, 2027657]
  vec32b0 = 0x006ee8370037dd5100744b9400676dfe005fbd2e001f6b94003b4ebf001ef089
*/
vec32b0_bnmulvm:
  .word 0x001ef089
  .word 0x003b4ebf
  .word 0x001f6b94
  .word 0x005fbd2e
  .word 0x00676dfe
  .word 0x00744b94
  .word 0x0037dd51
  .word 0x006ee837

/*
  Result of 32bit mulvm
  res = [1620927, 7309254, 1234587, 1342470, 3140778, 8169851, 1752570, 480708]
  res = 0x0018bbbf006f87c60012d69b00147c06002fecaa007ca97b001abdfa000755c4
*/

/*
  Result of 32bit mulvm without conditional subtraction
  res = [1620927, 7309254, 1234587, 1342470, 3140778, 8169851, 1752570, 480708]
  res = 0x0018bbbf006f87c60012d69b00147c06002fecaa007ca97b001abdfa000755c4
*/

/*
  32bit vector mod32 for instruction mulvml. Combined [R, q]
  mod32 = [4236238847, 8380417]
  mod32 = 0x000000000000000000000000000000000000000000000000fc7fdfff007fe001
*/
mod32_bnmulvml:
  .word 0x007fe001
  .word 0xfc7fdfff
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/*
  32bit vector vec32a for instruction mulvlm
  vec32a = [4386494, 351607, 6259716, 5199533, 2908764, 4819738, 3847752, 1371499]
  vec32a = 0x0042eebe00055d77005f8404004f56ad002c625c00498b1a003ab6480014ed6b
*/
vec32a_bnmulvml:
  .word 0x0014ed6b
  .word 0x003ab648
  .word 0x00498b1a
  .word 0x002c625c
  .word 0x004f56ad
  .word 0x005f8404
  .word 0x00055d77
  .word 0x0042eebe

/*
  32bit vector vec32b for instruction mulvlm
  vec32b = [5579227, 5963489, 3458491, 7380290, 3431077, 8342412, 2134462, 7944091]
  vec32b = 0x005521db005afee10034c5bb00709d4200345aa5007f4b8c002091be0079379b
*/
vec32b_bnmulvml:
  .word 0x0079379b
  .word 0x002091be
  .word 0x007f4b8c
  .word 0x00345aa5
  .word 0x00709d42
  .word 0x0034c5bb
  .word 0x005afee1
  .word 0x005521db
/*
  Result of 32bit mulvlm index 0
  res = [515442, 718185, 5498530, 8237924, 2044754, 1726077, 6572625, 3330118]
  res = 0x0007dd72000af5690053e6a2007db364001f3352001a567d00644a510032d046

  Result of 32bit mulvlm index 1
  res = [5419054, 1425467, 3766569, 6818953, 4725646, 2800241, 4192112, 6140848]
  res = 0x0052b02e0015c03b0039792900680c8900481b8e002aba71003ff770005db3b0

  Result of 32bit mulvlm index 2
  res = [3018797, 4432770, 8337926, 4779507, 5619268, 5774263, 722707, 754865]
  res = 0x002e102d0043a382007f3a060048edf30055be4400581bb7000b0713000b84b1

  Result of 32bit mulvlm index 3
  res = [7198082, 4470350, 1294493, 652760, 6695655, 6942087, 1374687, 3415932]
  res = 0x006dd5820044364e0013c09d0009f5d800662ae70069ed870014f9df00341f7c

  Result of 32bit mulvlm index 4
  res = [4028494, 3561434, 1255813, 1531198, 1806146, 7587267, 4810729, 2052119]
  res = 0x003d784e003657da0013298500175d3e001b8f420073c5c3004967e9001f5017

  Result of 32bit mulvlm index 5
  res = [3946449, 1256339, 5192417, 7420002, 7942467, 4331764, 4009735, 7997143]
  res = 0x003c37d100132b93004f3ae10071386200793143004218f4003d2f07007a06d7

  Result of 32bit mulvlm index 6
  res = [7645843, 696628, 2618429, 6339788, 59635, 120462, 2282714, 5805869]
  res = 0x0074aa93000aa1340027f43d0060bccc0000e8f30001d68e0022d4da0058972d

  Result of 32bit mulvlm index 7
  res = [1268083, 1404023, 6310330, 5756485, 6378028, 3750173, 8235518, 7687323]
  res = 0x0013597300156c77006049ba0057d6450061522c0039391d007da9fe00754c9b
*/

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
vecA_bnpack:
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
  .word 0xFECCDDEE
vecB_bnpack:
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
  .word 0xFEAABBAA
vecC_bnpack:
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
  .word 0xFE33FF33
vecD_bnpack:
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577
  .word 0xFE775577

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
vec1_bnunpk:
  .word 0xEECCDDEE
  .word 0xDDEECCDD
  .word 0xCCDDEECC
  .word 0xEECCDDEE
  .word 0xDDEECCDD
  .word 0xCCDDEECC
  .word 0xAAAABBAA
  .word 0xBBAAAABB
vec2_bnunpk:
  .word 0xAABBAAAA
  .word 0xAAAABBAA
  .word 0xBBAAAABB
  .word 0xAABBAAAA
  .word 0x3333FF33
  .word 0xFF3333FF
  .word 0x33FF3333
  .word 0x3333FF33
vec3_bnunpk:
  .word 0xFF3333FF
  .word 0x33FF3333
  .word 0x77775577
  .word 0x55777755
  .word 0x77557777
  .word 0x77775577
  .word 0x55777755
  .word 0x77557777
