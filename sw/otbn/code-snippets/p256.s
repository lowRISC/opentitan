/* Copyright lowRISC Contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_p256.c
 */

.globl p256init
.globl p256isoncurve
.globl p256scalarmult
.globl p256sign
.globl p256verify

.text

SetupP256PandMuLow:
  sw x0, 524(x0)
  sw x0, 528(x0)
  sw x0, 532(x0)
  addi x2, x0, 1
  sw x2, 536(x0)
  addi x2, x0, -1
  sw x2, 512(x0)
  sw x2, 516(x0)
  sw x2, 520(x0)
  sw x2, 540(x0)
  addi x2, x0, 29
  bn.lid x2, 512(x0)
  bn.wsrw 0, w29
  sw x0, 548(x0)
  sw x0, 572(x0)
  addi x2, x0, -1
  sw x2, 552(x0)
  sw x2, 568(x0)
  addi x2, x0, 3
  sw x2, 544(x0)
  addi x2, x0, -2
  sw x2, 556(x0)
  sw x2, 560(x0)
  sw x2, 564(x0)
  addi x2, x0, 28
  bn.lid x2, 544(x0)
  jalr x0, x1, 0

p256init:
  addi x3, x0, 31
  bn.lid x3, 0(x0)
  bn.xor w31, w31, w31
  bn.addi w30, w31, 1
  jal x1, SetupP256PandMuLow
  lui x2, 163110
  addi x2, x2, 75
  sw x2, 576(x0)
  lui x2, 244964
  addi x2, x2, -962
  sw x2, 580(x0)
  lui x2, 836923
  addi x2, x2, 246
  sw x2, 584(x0)
  lui x2, 414160
  addi x2, x2, 1712
  sw x2, 588(x0)
  lui x2, 485768
  addi x2, x2, 1724
  sw x2, 592(x0)
  lui x2, 736956
  addi x2, x2, -683
  sw x2, 596(x0)
  lui x2, 697257
  addi x2, x2, 999
  sw x2, 600(x0)
  lui x2, 371811
  addi x2, x2, 1496
  sw x2, 604(x0)
  addi x2, x0, 27
  bn.lid x2, 576(x0)
  jalr x0, x1, 0

MulMod:
  bn.mulqacc.z w24.0, w25.0, 0
  bn.mulqacc w24.1, w25.0, 64
  bn.mulqacc.so w19.l, w24.0, w25.1, 64
  bn.mulqacc w24.2, w25.0, 0
  bn.mulqacc w24.1, w25.1, 0
  bn.mulqacc w24.0, w25.2, 0
  bn.mulqacc w24.3, w25.0, 64
  bn.mulqacc w24.2, w25.1, 64
  bn.mulqacc w24.1, w25.2, 64
  bn.mulqacc.so w19.u, w24.0, w25.3, 64
  bn.mulqacc w24.3, w25.1, 0
  bn.mulqacc w24.2, w25.2, 0
  bn.mulqacc w24.1, w25.3, 0
  bn.mulqacc w24.3, w25.2, 64
  bn.mulqacc.so w20.l, w24.2, w25.3, 64
  bn.mulqacc.so w20.u, w24.3, w25.3, 0
  bn.add w20, w20, w31
  bn.sel w22, w28, w31, M
  bn.rshi w21, w20, w19 >> 255
  bn.mulqacc.z w21.0, w28.0, 0
  bn.mulqacc w21.1, w28.0, 64
  bn.mulqacc.so w23.l, w21.0, w28.1, 64
  bn.mulqacc w21.2, w28.0, 0
  bn.mulqacc w21.1, w28.1, 0
  bn.mulqacc w21.0, w28.2, 0
  bn.mulqacc w21.3, w28.0, 64
  bn.mulqacc w21.2, w28.1, 64
  bn.mulqacc w21.1, w28.2, 64
  bn.mulqacc.so w23.u, w21.0, w28.3, 64
  bn.mulqacc w21.3, w28.1, 0
  bn.mulqacc w21.2, w28.2, 0
  bn.mulqacc w21.1, w28.3, 0
  bn.mulqacc w21.3, w28.2, 64
  bn.mulqacc.so w24.l, w21.2, w28.3, 64
  bn.mulqacc.so w24.u, w21.3, w28.3, 0
  bn.add w20, w20, w31
  bn.rshi w25, w31, w20 >> 255
  bn.add w24, w24, w21
  bn.addc w25, w25, w31
  bn.add w24, w24, w22
  bn.addc w25, w25, w31
  bn.rshi w21, w25, w24 >> 1
  bn.mulqacc.z w29.0, w21.0, 0
  bn.mulqacc w29.1, w21.0, 64
  bn.mulqacc.so w22.l, w29.0, w21.1, 64
  bn.mulqacc w29.2, w21.0, 0
  bn.mulqacc w29.1, w21.1, 0
  bn.mulqacc w29.0, w21.2, 0
  bn.mulqacc w29.3, w21.0, 64
  bn.mulqacc w29.2, w21.1, 64
  bn.mulqacc w29.1, w21.2, 64
  bn.mulqacc.so w22.u, w29.0, w21.3, 64
  bn.mulqacc w29.3, w21.1, 0
  bn.mulqacc w29.2, w21.2, 0
  bn.mulqacc w29.1, w21.3, 0
  bn.mulqacc w29.3, w21.2, 64
  bn.mulqacc.so w23.l, w29.2, w21.3, 64
  bn.mulqacc.so w23.u, w29.3, w21.3, 0
  bn.add w23, w23, w31
  bn.sub w22, w19, w22
  bn.subb w20, w20, w23
  bn.sel w21, w29, w31, L
  bn.sub w21, w22, w21
  bn.addm w19, w21, w31
  jalr x0, x1, 0

p256isoncurve:
  addi x3, x0, 0
  bn.lid x3, 0(x0)
  lw x16, 0(x0)
  lw x17, 4(x0)
  lw x18, 8(x0)
  lw x19, 12(x0)
  lw x20, 16(x0)
  lw x21, 20(x0)
  lw x22, 24(x0)
  lw x23, 28(x0)
  addi x8, x0, 0
  lw x9, 4(x0)
  lw x10, 8(x0)
  lw x11, 12(x0)
  lw x12, 16(x0)
  addi x13, x0, 24
  addi x14, x0, 24
  lw x15, 28(x0)
  bn.lid x14, 0(x22)
  bn.mov w25, w24
  jal x1, MulMod
  bn.mov w0, w19
  bn.lid x13, 0(x21)
  bn.mov w25, w24
  jal x1, MulMod
  bn.lid x13, 0(x21)
  bn.mov w25, w19
  jal x1, MulMod
  bn.lid x13, 0(x21)
  bn.subm w19, w19, w24
  bn.subm w19, w19, w24
  bn.subm w19, w19, w24
  bn.addm w24, w19, w27
  bn.sid x13, 0(x19)
  bn.sid x8, 0(x20)
  jalr x0, x1, 0

ProjAdd:
  bn.mov w24, w11
  bn.mov w25, w8
  jal x1, MulMod
  bn.mov w14, w19
  bn.mov w24, w12
  bn.mov w25, w9
  jal x1, MulMod
  bn.mov w15, w19
  bn.mov w24, w13
  bn.mov w25, w10
  jal x1, MulMod
  bn.mov w16, w19
  bn.addm w17, w11, w12
  bn.addm w18, w8, w9
  bn.mov w24, w17
  bn.mov w25, w18
  jal x1, MulMod
  bn.addm w18, w14, w15
  bn.subm w17, w19, w18
  bn.addm w18, w12, w13
  bn.addm w19, w9, w10
  bn.mov w24, w18
  bn.mov w25, w19
  jal x1, MulMod
  bn.mov w18, w19
  bn.addm w19, w15, w16
  bn.subm w18, w18, w19
  bn.addm w19, w11, w13
  bn.addm w12, w8, w10
  bn.mov w24, w19
  bn.mov w25, w12
  jal x1, MulMod
  bn.mov w11, w19
  bn.addm w12, w14, w16
  bn.subm w12, w11, w12
  bn.mov w24, w27
  bn.mov w25, w16
  jal x1, MulMod
  bn.subm w11, w12, w19
  bn.addm w13, w11, w11
  bn.addm w11, w11, w13
  bn.subm w13, w15, w11
  bn.addm w11, w15, w11
  bn.mov w24, w27
  bn.mov w25, w12
  jal x1, MulMod
  bn.addm w15, w16, w16
  bn.addm w16, w15, w16
  bn.subm w12, w19, w16
  bn.subm w12, w12, w14
  bn.addm w15, w12, w12
  bn.addm w12, w15, w12
  bn.addm w15, w14, w14
  bn.addm w14, w15, w14
  bn.subm w14, w14, w16
  bn.mov w24, w18
  bn.mov w25, w12
  jal x1, MulMod
  bn.mov w15, w19
  bn.mov w24, w14
  bn.mov w25, w12
  jal x1, MulMod
  bn.mov w16, w19
  bn.mov w24, w11
  bn.mov w25, w13
  jal x1, MulMod
  bn.addm w12, w19, w16
  bn.mov w24, w17
  bn.mov w25, w11
  jal x1, MulMod
  bn.subm w11, w19, w15
  bn.mov w24, w18
  bn.mov w25, w13
  jal x1, MulMod
  bn.mov w13, w19
  bn.mov w24, w17
  bn.mov w25, w14
  jal x1, MulMod
  bn.addm w13, w13, w19
  jalr x0, x1, 0

ProjToAffine:
  bn.addm w10, w10, w31
  bn.mov w24, w10
  bn.mov w25, w10
  jal x1, MulMod
  bn.mov w24, w19
  bn.mov w25, w10
  jal x1, MulMod
  bn.mov w12, w19
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  bn.mov w24, w19
  bn.mov w25, w12
  jal x1, MulMod
  bn.mov w13, w19
  loopi 4, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w24, w19
  bn.mov w25, w13
  jal x1, MulMod
  bn.mov w14, w19
  loopi 8, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w24, w19
  bn.mov w25, w14
  jal x1, MulMod
  bn.mov w15, w19
  loopi 16, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w24, w19
  bn.mov w25, w15
  jal x1, MulMod
  bn.mov w16, w19
  loopi 32, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w17, w19
  bn.mov w24, w10
  bn.mov w25, w19
  jal x1, MulMod
  loopi 192, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w18, w19
  bn.mov w24, w17
  bn.mov w25, w16
  jal x1, MulMod
  loopi 16, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w24, w15
  bn.mov w25, w19
  jal x1, MulMod
  loopi 8, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w24, w14
  bn.mov w25, w19
  jal x1, MulMod
  loopi 4, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w24, w13
  bn.mov w25, w19
  jal x1, MulMod
  loopi 2, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w24, w12
  bn.mov w25, w19
  jal x1, MulMod
  loopi 2, 4
  bn.mov w24, w19
  bn.mov w25, w19
  jal x1, MulMod
  addi x0, x0, 0
  bn.mov w24, w10
  bn.mov w25, w19
  jal x1, MulMod
  bn.mov w24, w19
  bn.mov w25, w18
  jal x1, MulMod
  bn.mov w14, w19
  bn.mov w24, w8
  bn.mov w25, w14
  jal x1, MulMod
  bn.mov w11, w19
  bn.mov w24, w9
  bn.mov w25, w14
  jal x1, MulMod
  bn.mov w12, w19
  jalr x0, x1, 0

ModInv:
  bn.wsrr w2, 0
  bn.subi w2, w2, 2
  bn.mov w1, w30
  loopi 256, 14
  bn.mov w24, w1
  bn.mov w25, w1
  jal x1, MulMod
  bn.mov w3, w19
  bn.add w2, w2, w2
  bn.sel w1, w1, w3, C
  csrrs x2, 1984, x0
  andi x2, x2, 1
  beq x2, x0, nomul
  bn.mov w24, w3
  bn.mov w25, w0
  jal x1, MulMod
  bn.mov w1, w19
  nomul:
  addi x0, x0, 0
  jalr x0, x1, 0

FetchBandRandomize:
  bn.wsrr w2, 1
  bn.addm w26, w2, w31
  bn.lid x10, 0(x21)
  bn.mov w25, w26
  jal x1, MulMod
  bn.mov w6, w19
  bn.lid x10, 0(x22)
  bn.mov w25, w26
  jal x1, MulMod
  bn.mov w7, w19
  jalr x0, x1, 0

ProjDouble:
  bn.mov w11, w8
  bn.mov w12, w9
  bn.mov w13, w10
  jal x1, ProjAdd
  jalr x0, x1, 0

SetupP256NandMuLow:
  addi x2, x0, 0
  sw x2, 632(x0)
  addi x2, x2, -1
  sw x2, 624(x0)
  sw x2, 628(x0)
  sw x2, 636(x0)
  lui x2, 1033778
  addi x2, x2, 1361
  sw x2, 608(x0)
  lui x2, 998301
  addi x2, x2, -1342
  sw x2, 612(x0)
  lui x2, 684410
  addi x2, x2, -380
  sw x2, 616(x0)
  lui x2, 773744
  addi x2, x2, -1363
  sw x2, 620(x0)
  addi x2, x0, 29
  bn.lid x2, 608(x0)
  bn.wsrw 0, w29
  addi x2, x0, 0
  sw x2, 668(x0)
  addi x2, x0, -1
  sw x2, 656(x0)
  sw x2, 664(x0)
  addi x2, x0, -2
  sw x2, 660(x0)
  lui x2, 978426
  addi x2, x2, -1026
  sw x2, 640(x0)
  lui x2, 4864
  addi x2, x2, -635
  sw x2, 644(x0)
  lui x2, 913831
  addi x2, x2, -991
  sw x2, 648(x0)
  lui x2, 274832
  addi x2, x2, 1362
  sw x2, 652(x0)
  addi x2, x0, 28
  bn.lid x2, 640(x0)
  jalr x0, x1, 0

ScalarMult_internal:
  jal x1, SetupP256NandMuLow
  bn.lid x9, 0(x17)
  bn.addm w1, w1, w31
  bn.subm w0, w0, w1
  jal x1, SetupP256PandMuLow
  jal x1, FetchBandRandomize
  bn.mov w8, w6
  bn.mov w9, w7
  bn.mov w10, w26
  jal x1, ProjDouble
  bn.mov w3, w11
  bn.mov w4, w12
  bn.mov w5, w13
  bn.mov w8, w31
  bn.mov w9, w30
  bn.mov w10, w31
  loopi 256, 32
  jal x1, ProjDouble
  jal x1, FetchBandRandomize
  bn.xor w8, w0, w1
  bn.sel w8, w6, w3, M
  bn.sel w9, w7, w4, M
  bn.sel w10, w26, w5, M
  bn.mov w2, w11
  bn.mov w6, w12
  bn.mov w7, w13
  jal x1, ProjAdd
  bn.or w8, w0, w1
  bn.sel w8, w11, w2, M
  bn.sel w9, w12, w6, M
  bn.sel w10, w13, w7, M
  bn.rshi w0, w0, w0 >> 255
  bn.rshi w1, w1, w1 >> 255
  bn.wsrr w11, 1
  bn.wsrr w12, 1
  bn.wsrr w13, 1
  bn.wsrr w2, 1
  bn.mov w24, w3
  bn.mov w25, w2
  jal x1, MulMod
  bn.mov w3, w19
  bn.mov w24, w4
  bn.mov w25, w2
  jal x1, MulMod
  bn.mov w4, w19
  bn.mov w24, w5
  bn.mov w25, w2
  jal x1, MulMod
  bn.mov w5, w19
  jal x1, ProjToAffine
  jalr x0, x1, 0

get_P256B:
  lui x2, 887180
  addi x2, x2, 662
  sw x2, 672(x0)
  lui x2, 1002004
  addi x2, x2, -1723
  sw x2, 676(x0)
  lui x2, 188083
  addi x2, x2, 928
  sw x2, 680(x0)
  lui x2, 487480
  addi x2, x2, -639
  sw x2, 684(x0)
  lui x2, 408132
  addi x2, x2, 242
  sw x2, 688(x0)
  lui x2, 1018830
  addi x2, x2, 1765
  sw x2, 692(x0)
  lui x2, 922308
  addi x2, x2, 583
  sw x2, 696(x0)
  lui x2, 438653
  addi x2, x2, 498
  sw x2, 700(x0)
  addi x2, x0, 8
  bn.lid x2, 672(x0)
  lui x2, 228341
  addi x2, x2, 501
  sw x2, 704(x0)
  lui x2, 834404
  addi x2, x2, 104
  sw x2, 708(x0)
  lui x2, 439062
  addi x2, x2, -306
  sw x2, 712(x0)
  lui x2, 179427
  addi x2, x2, 855
  sw x2, 716(x0)
  lui x2, 508154
  addi x2, x2, -490
  sw x2, 720(x0)
  lui x2, 585343
  addi x2, x2, -1206
  sw x2, 724(x0)
  lui x2, 1040808
  addi x2, x2, -101
  sw x2, 728(x0)
  lui x2, 327220
  addi x2, x2, 738
  sw x2, 732(x0)
  addi x2, x0, 9
  bn.lid x2, 704(x0)
  jalr x0, x1, 0

p256sign:
  addi x0, x0, 0
  addi x3, x0, 0
  bn.lid x3, 0(x0)
  lw x16, 0(x0)
  lw x17, 4(x0)
  lw x18, 8(x0)
  lw x19, 12(x0)
  lw x20, 16(x0)
  lw x21, 20(x0)
  lw x22, 24(x0)
  lw x23, 28(x0)
  addi x8, x0, 0
  addi x9, x0, 1
  addi x10, x0, 24
  lw x11, 12(x0)
  addi x12, x0, 8
  addi x13, x0, 9
  lw x14, 24(x0)
  lw x15, 28(x0)
  jal x1, get_P256B
  bn.sid x12, 0(x21)
  bn.sid x13, 0(x22)
  addi x0, x0, 0
  bn.lid x8, 0(x16)
  jal x1, ScalarMult_internal
  jal x1, SetupP256NandMuLow
  bn.lid x8, 0(x16)
  jal x1, ModInv
  bn.lid x10, 0(x23)
  bn.mov w25, w1
  jal x1, MulMod
  bn.addm w24, w11, w31
  bn.sid x10, 0(x19)
  addi x0, x0, 0
  bn.mov w25, w19
  jal x1, MulMod
  bn.mov w0, w19
  bn.lid x10, 0(x18)
  bn.mov w25, w1
  jal x1, MulMod
  bn.addm w0, w19, w0
  bn.sid x8, 0(x20)
  jal x1, SetupP256PandMuLow
  jalr x0, x1, 0

p256scalarbasemult:
  addi x0, x0, 0
  addi x3, x0, 0
  bn.lid x3, 0(x0)
  lw x16, 0(x0)
  lw x17, 4(x0)
  lw x18, 8(x0)
  lw x19, 12(x0)
  lw x20, 16(x0)
  lw x21, 20(x0)
  lw x22, 24(x0)
  lw x23, 28(x0)
  addi x8, x0, 0
  addi x9, x0, 1
  addi x10, x0, 24
  addi x11, x0, 11
  addi x12, x0, 8
  addi x13, x0, 9
  lw x14, 24(x0)
  lw x15, 28(x0)
  bn.lid x8, 0(x17)
  jal x1, get_P256B
  bn.sid x12, 0(x21)
  bn.sid x13, 0(x22)
  addi x0, x0, 0
  bn.lid x8, 0(x23)
  jal x1, ScalarMult_internal
  bn.sid x11++, 0(x21)
  bn.sid x11++, 0(x22)
  jalr x0, x1, 0

ModInvVar:
  bn.mov w2, w31
  bn.mov w3, w30
  bn.wsrr w4, 0
  bn.wsrr w7, 0
  bn.mov w5, w0

impvt_Loop:
  bn.or w4, w4, w4
  csrrs x2, 1984, x0
  andi x2, x2, 4
  bne x2, x0, impvt_Uodd
  bn.rshi w4, w31, w4 >> 1
  bn.or w2, w2, w2
  csrrs x2, 1984, x0
  andi x2, x2, 4
  bne x2, x0, impvt_Rodd
  bn.rshi w2, w31, w2 >> 1
  jal x0, impvt_Loop

impvt_Rodd:
  bn.add w2, w7, w2
  bn.addc w6, w31, w31
  bn.rshi w2, w6, w2 >> 1
  jal x0, impvt_Loop

impvt_Uodd:
  bn.or w5, w5, w5
  csrrs x2, 1984, x0
  andi x2, x2, 4
  bne x2, x0, impvt_UVodd
  bn.rshi w5, w31, w5 >> 1
  bn.or w3, w3, w3
  csrrs x2, 1984, x0
  andi x2, x2, 4
  bne x2, x0, impvt_Sodd
  bn.rshi w3, w31, w3 >> 1
  jal x0, impvt_Loop

impvt_Sodd:
  bn.add w3, w7, w3
  bn.addc w6, w31, w31
  bn.rshi w3, w6, w3 >> 1
  jal x0, impvt_Loop

impvt_UVodd:
  bn.cmp w5, w4
  csrrs x2, 1984, x0
  andi x2, x2, 1
  beq x2, x0, impvt_V_gte_U
  bn.subm w2, w2, w3
  bn.sub w4, w4, w5
  jal x0, impvt_Loop

impvt_V_gte_U:
  bn.subm w3, w3, w2
  bn.sub w5, w5, w4
  csrrs x2, 1984, x0
  andi x2, x2, 8
  beq x2, x0, impvt_Loop
  bn.addm w1, w2, w31
  jalr x0, x1, 0

p256verify:
  addi x3, x0, 6
  bn.lid x3, 0(x0)
  lw x16, 0(x0)
  lw x17, 4(x0)
  lw x18, 8(x0)
  lw x19, 12(x0)
  lw x20, 16(x0)
  lw x21, 20(x0)
  lw x22, 24(x0)
  lw x23, 28(x0)
  addi x8, x0, 11
  lw x9, 4(x0)
  addi x10, x0, 24
  addi x11, x0, 24
  addi x12, x0, 0
  addi x13, x0, 8
  addi x14, x0, 9
  addi x15, x0, 12
  bn.lid x11, 0(x19)
  bn.mov w24, w6
  bn.not w24, w24
  jal x1, SetupP256NandMuLow
  bn.cmp w6, w31
  csrrs x2, 1984, x0
  andi x2, x2, 8
  bne x2, x0, fail
  bn.cmp w6, w29
  csrrs x2, 1984, x0
  andi x2, x2, 1
  beq x2, x0, fail
  bn.lid x12, 0(x20)
  bn.cmp w0, w31
  csrrs x2, 1984, x0
  andi x2, x2, 8
  bne x2, x0, fail
  bn.cmp w0, w29
  csrrs x2, 1984, x0
  andi x2, x2, 1
  beq x2, x0, fail
  jal x1, ModInvVar
  bn.lid x11, 0(x19)
  bn.mov w25, w1
  jal x1, MulMod
  bn.mov w0, w19
  bn.lid x10, 0(x18)
  bn.mov w25, w1
  jal x1, MulMod
  bn.mov w1, w19
  jal x1, SetupP256PandMuLow
  bn.lid x8, 0(x21)
  bn.lid x15, 0(x22)
  bn.mov w13, w30
  jal x1, get_P256B
  bn.mov w10, w30
  jal x1, ProjAdd
  bn.mov w3, w11
  bn.mov w4, w12
  bn.mov w5, w13
  bn.and w2, w0, w1
  bn.mov w11, w31
  bn.mov w12, w30
  bn.mov w13, w31
  loopi 256, 30
  bn.mov w8, w11
  bn.mov w9, w12
  bn.mov w10, w13
  jal x1, ProjAdd
  bn.add w2, w2, w2
  csrrs x2, 1984, x0
  andi x2, x2, 1
  beq x2, x0, noBoth
  bn.mov w8, w3
  bn.mov w9, w4
  bn.mov w10, w5
  jal x1, ProjAdd
  jal x0, noY

noBoth:
  bn.add w6, w0, w0
  csrrs x2, 1984, x0
  andi x2, x2, 1
  beq x2, x0, noG
  bn.lid x13, 0(x21)
  bn.lid x14, 0(x22)
  bn.mov w10, w30
  jal x1, ProjAdd

noG:
  bn.add w6, w1, w1
  csrrs x2, 1984, x0
  andi x2, x2, 1
  beq x2, x0, noY
  jal x1, get_P256B
  bn.mov w10, w30
  jal x1, ProjAdd

noY:
  bn.add w0, w0, w0
  bn.add w1, w1, w1
  bn.mov w0, w13
  jal x1, ModInvVar
  bn.mov w24, w1
  bn.mov w25, w11
  jal x1, MulMod
  jal x1, SetupP256NandMuLow
  bn.subm w24, w19, w31

fail:
  bn.sid x11, 0(x17)
  jalr x0, x1, 0

p256scalarmult:
  addi x3, x0, 0
  bn.lid x3, 0(x0)
  lw x16, 0(x0)
  lw x17, 4(x0)
  lw x18, 8(x0)
  lw x19, 12(x0)
  lw x20, 16(x0)
  lw x21, 20(x0)
  lw x22, 24(x0)
  lw x23, 28(x0)
  addi x8, x0, 0
  addi x9, x0, 1
  addi x10, x0, 24
  addi x11, x0, 11
  lw x12, 16(x0)
  lw x13, 20(x0)
  lw x14, 24(x0)
  lw x15, 28(x0)
  bn.lid x8, 0(x16)
  jal x1, ScalarMult_internal
  bn.sid x11++, 0(x21)
  bn.sid x11++, 0(x22)
  jalr x0, x1, 0
