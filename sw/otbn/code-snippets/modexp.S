/* Copyright lowRISC Contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 *
 *	https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c
 *
 */
d0inv:
BN.XOR w0, w0, w0
BN.ADDI w0, w0, 1
BN.MOV w29, w0
LOOPI 256, 13
BN.MULQACC.Z w28.0, w29.0, 0
BN.MULQACC w28.1, w29.0, 64
BN.MULQACC.SO w1.L, w28.0, w29.1, 64
BN.MULQACC w28.2, w29.0, 0
BN.MULQACC w28.1, w29.1, 0
BN.MULQACC w28.0, w29.2, 0
BN.MULQACC w28.3, w29.0, 64
BN.MULQACC w28.2, w29.1, 64
BN.MULQACC w28.1, w29.2, 64
BN.MULQACC.SO w1.U, w28.0, w29.3, 64
BN.AND w1, w1, w0
BN.OR w29, w29, w1
BN.ADD w0, w0, w0
BN.SUB w29, w31, w29
JALR x0, x1, 0

selcxSub:
ADDI x8, x0, 5
ADDI x10, x0, 3
ADDI x11, x0, 2
ADDI x12, x0, 4
LW x16, 0(x0)
BN.WSRRS w4, 1, w31
BN.ADD w4, w4, w31
CSRRS x2, 1984, x0
ANDI x2, x2, 2
BNE x2, x0, selcxSub_invsel
BN.ADDC w3, w4, w4 << 16B, FG1
LOOP x30, 7
BN.LID x10, 0(x16++)
BN.MOVR x11, x8
BN.MOVR x8, x12
BN.SUBB w4, w2, w3
BN.WSRRS w3, 1, w31
BN.SEL w3, w4, w2, FG1.L
BN.MOVR x8++, x10
JALR x0, x1, 0

selcxSub_invsel:
BN.ADDC w3, w4, w4 << 16B, FG1
LOOP x30, 7
BN.LID x10, 0(x16++)
BN.MOVR x11, x8
BN.MOVR x8, x12
BN.SUBB w4, w2, w3
BN.WSRRS w3, 1, w31
BN.SEL w3, w2, w4, FG1.L
BN.MOVR x8++, x10
JALR x0, x1, 0

computeRR:
BN.XOR w31, w31, w31
ADDI x3, x0, 0
BN.LID x3, 0(x0)
LW x16, 0(x0)
LW x17, 4(x0)
LW x18, 8(x0)
LW x19, 12(x0)
LW x20, 16(x0)
LW x21, 20(x0)
LW x22, 24(x0)
LW x23, 28(x0)
BN.XOR w3, w3, w3
SLLI x24, x22, 8
ADDI x8, x0, 5
ADDI x10, x0, 3
BN.XOR w3, w3, w3
LOOP x30, 1
BN.MOVR x8++, x10
BN.SUB w3, w31, w0, FG1
JAL x1, selcxSub
LOOP x24, 16
ADDI x8, x0, 5
BN.SUB w3, w3, w3, FG1
LOOP x30, 3
BN.MOVR x11, x8
BN.ADDC w2, w2, w2, FG1
BN.MOVR x8++, x11
JAL x1, selcxSub
ADDI x8, x0, 5
LW x16, 0(x0)
BN.SUB w3, w3, w3, FG1
LOOP x30, 3
BN.LID x10, 0(x16++)
BN.MOVR x11, x8++
BN.CMPB w3, w2, FG1
JAL x1, selcxSub
ADDI x0, x0, 0
ADDI x8, x0, 5
LOOP x30, 2
BN.SID x8, 0(x18++)
ADDI x8, x8, 1
JALR x0, x1, 0

dmXd0:
BN.MULQACC.Z w30.0, w25.0, 0
BN.MULQACC w30.1, w25.0, 64
BN.MULQACC.SO w27.L, w30.0, w25.1, 64
BN.MULQACC w30.2, w25.0, 0
BN.MULQACC w30.1, w25.1, 0
BN.MULQACC w30.0, w25.2, 0
BN.MULQACC w30.3, w25.0, 64
BN.MULQACC w30.2, w25.1, 64
BN.MULQACC w30.1, w25.2, 64
BN.MULQACC.SO w27.U, w30.0, w25.3, 64
BN.MULQACC w30.3, w25.1, 0
BN.MULQACC w30.2, w25.2, 0
BN.MULQACC w30.1, w25.3, 0
BN.MULQACC w30.3, w25.2, 64
BN.MULQACC.SO w26.L, w30.2, w25.3, 64
BN.MULQACC.SO w26.U, w30.3, w25.3, 0
JALR x0, x1, 0

dmXa:
BN.MULQACC.Z w30.0, w2.0, 0
BN.MULQACC w30.1, w2.0, 64
BN.MULQACC.SO w27.L, w30.0, w2.1, 64
BN.MULQACC w30.2, w2.0, 0
BN.MULQACC w30.1, w2.1, 0
BN.MULQACC w30.0, w2.2, 0
BN.MULQACC w30.3, w2.0, 64
BN.MULQACC w30.2, w2.1, 64
BN.MULQACC w30.1, w2.2, 64
BN.MULQACC.SO w27.U, w30.0, w2.3, 64
BN.MULQACC w30.3, w2.1, 0
BN.MULQACC w30.2, w2.2, 0
BN.MULQACC w30.1, w2.3, 0
BN.MULQACC w30.3, w2.2, 64
BN.MULQACC.SO w26.L, w30.2, w2.3, 64
BN.MULQACC.SO w26.U, w30.3, w2.3, 0
JALR x0, x1, 0

mma_sub_cx:
BN.WSRRS w28, 1, w31
BN.ADD w28, w28, w31
CSRRS x2, 1984, x0
ANDI x2, x2, 2
BNE x2, x0, mma_invsel
BN.ADDC w28, w28, w28 << 16B, FG1
LOOP x30, 7
BN.LID x13, 0(x16++)
BN.MOVR x12, x8
BN.SUBB w29, w30, w24
BN.WSRRS w24, 1, w31
BN.MOVR x8, x13
BN.SEL w24, w29, w30, FG1.L
BN.MOVR x8++, x13
JALR x0, x1, 0

mma_invsel:
BN.ADDC w28, w28, w28 << 16B, FG1
LOOP x30, 7
BN.LID x13, 0(x16++)
BN.MOVR x12, x8
BN.SUBB w29, w30, w24
BN.WSRRS w24, 1, w31
BN.MOVR x8, x13
BN.SEL w24, w30, w29, FG1.L
BN.MOVR x8++, x13
JALR x0, x1, 0

mma:
ADDI x12, x0, 30
ADDI x13, x0, 24
ADDI x8, x0, 4
ADDI x10, x0, 4
BN.LID x12, 0(x19++)
JAL x1, dmXa
BN.MOVR x13, x8++
BN.ADD w30, w27, w24
BN.ADDC w29, w26, w31
BN.MOV w25, w3
JAL x1, dmXd0
BN.MOV w25, w27
BN.MOV w28, w26
BN.MOV w24, w30
BN.LID x12, 0(x16++)
JAL x1, dmXd0
BN.ADD w27, w27, w24
BN.ADDC w28, w26, w31
LOOP x31, 14
BN.LID x12, 0(x19++)
JAL x1, dmXa
BN.MOVR x13, x8++
BN.ADD w27, w27, w24
BN.ADDC w26, w26, w31
BN.ADD w24, w27, w29
BN.ADDC w29, w26, w31
BN.LID x12, 0(x16++)
JAL x1, dmXd0
BN.ADD w27, w27, w24
BN.ADDC w26, w26, w31
BN.ADD w24, w27, w28, FG1
BN.MOVR x10++, x13
BN.ADDC w28, w26, w31, FG1

BN.ADDC w24, w29, w28, FG1
BN.MOVR x10++, x13
LW x16, 0(x0)
LW x19, 12(x0)
ADDI x8, x0, 4
ADDI x10, x0, 4
ADDI x12, x0, 30
ADDI x13, x0, 24
JAL x1, mma_sub_cx
ADDI x0, x0, 0
JALR x0, x1, 0

setupPtrs:
LW x16, 0(x0)
LW x17, 4(x0)
LW x18, 8(x0)
LW x19, 12(x0)
LW x20, 16(x0)
LW x21, 20(x0)
LW x22, 24(x0)
LW x23, 28(x0)
LW x24, 0(x0)
LW x25, 4(x0)
LW x26, 8(x0)
LW x27, 12(x0)
LW x28, 16(x0)
LW x29, 20(x0)
LW x30, 24(x0)
LW x31, 28(x0)
BN.MOV w1, w31
ADDI x8, x0, 4
ADDI x9, x0, 3
ADDI x10, x0, 4
ADDI x11, x0, 2
JALR x0, x1, 0

mulx:
ADDI x3, x0, 0
BN.LID x3, 0(x0)
JAL x1, setupPtrs
BN.LID x9, 0(x17)
BN.MOV w2, w31
LOOP x30, 1
BN.MOVR x10++, x11
ADDI x10, x0, 4
LOOP x30, 8
BN.LID x11, 0(x20++)
ADD x4, x16, x0
ADD x5, x19, x0
ADD x6, x20, x0
JAL x1, mma
ADD x16, x4, x0
ADD x19, x5, x0
ADD x20, x6, x0
ADDI x8, x0, 4
LOOP x30, 2
BN.SID x8, 0(x21++)
ADDI x8, x8, 1
ADDI x8, x0, 4
JALR x0, x1, 0

mm1_sub_cx:
BN.WSRRS w3, 1, w31
BN.ADD w3, w3, w31
CSRRS x2, 1984, x0
ANDI x2, x2, 2
BNE x2, x0, mm1_invsel
BN.ADDC w3, w3, w3 << 16B, FG1
LOOP x30, 6
BN.LID x9, 0(x16++)
BN.MOVR x11, x8++
BN.SUBB w3, w2, w3
BN.SEL w2, w3, w2, FG1.L
BN.SID x11, 0(x21++)
ADDI x0, x0, 0
JALR x0, x1, 0
ADDI x0, x0, 0

mm1_invsel:
BN.ADDC w3, w3, w3 << 16B, FG1
LOOP x30, 6
BN.LID x9, 0(x16++)
BN.MOVR x11, x8++
BN.SUBB w3, w2, w3
BN.SEL w2, w2, w3, FG1.L
BN.SID x11, 0(x21++)
ADDI x0, x0, 0
JALR x0, x1, 0

mul1_exp:
BN.LID x9, 0(x17)
BN.MOV w2, w31
LOOP x30, 1
BN.MOVR x10++, x11
BN.XOR w2, w2, w2
BN.ADDI w2, w2, 1
ADDI x6, x16, 0
ADDI x7, x19, 0
LOOP x30, 4
ADDI x16, x6, 0
ADDI x19, x7, 0
JAL x1, mma
BN.MOV w2, w31
ADDI x16, x6, 0
ADDI x19, x7, 0
BN.SUB w2, w2, w2, FG1
LOOP x30, 3
BN.LID x9, 0(x16++)
BN.MOVR x11, x8++
BN.CMPB w3, w2, FG1
ADDI x8, x0, 4
ADDI x10, x0, 4
ADDI x16, x6, 0
ADDI x19, x7, 0
JAL x1, mm1_sub_cx
ADDI x16, x6, 0
ADDI x19, x7, 0
JALR x0, x1, 0

mul1:
ADDI x3, x0, 0
BN.LID x3, 0(x0)
JAL x1, setupPtrs
JAL x1, mul1_exp
ECALL

sqrx_exp:
LW x16, 32(x0)
LW x17, 36(x0)
LW x18, 40(x0)
LW x19, 44(x0)
LW x20, 48(x0)
LW x21, 52(x0)
LW x22, 56(x0)
LW x23, 60(x0)
BN.LID x9, 0(x17)
BN.MOV w2, w31
LOOP x30, 1
BN.MOVR x10++, x11
LW x10, 8(x0)
LOOP x30, 8
BN.LID x11, 0(x20++)
ADDI x5, x20, 0
ADDI x6, x16, 0
ADDI x7, x19, 0
JAL x1, mma
ADDI x20, x5, 0
ADDI x16, x6, 0
ADDI x19, x7, 0
ADDI x10, x0, 4
ADDI x8, x0, 4
LOOP x30, 2
BN.SID x8, 0(x21++)
ADDI x8, x8, 1
ADDI x8, x0, 4
ADDI x10, x0, 4
LW x12, 16(x0)
LW x13, 20(x0)
JALR x0, x1, 0

mulx_exp:
LW x16, 64(x0)
LW x17, 68(x0)
LW x18, 72(x0)
LW x19, 76(x0)
LW x20, 80(x0)
LW x21, 84(x0)
LW x22, 88(x0)
LW x23, 92(x0)
BN.LID x9, 0(x17)
BN.MOV w2, w31
LOOP x30, 1
BN.MOVR x10++, x11
ADDI x8, x0, 4
ADDI x10, x0, 4
LW x12, 16(x0)
LW x13, 20(x0)
LOOP x30, 8
BN.LID x11, 0(x20++)
ADDI x5, x20, 0
ADDI x6, x16, 0
ADDI x7, x19, 0
JAL x1, mma
ADDI x20, x5, 0
ADDI x16, x6, 0
ADDI x19, x7, 0
ADDI x8, x0, 4
ADDI x10, x0, 4
LW x12, 16(x0)
LW x13, 20(x0)
JALR x0, x1, 0

selOutOrC:
BN.WSRRS w3, 1, w31
BN.OR w3, w3, w3
CSRRS x2, 1984, x0
ANDI x2, x2, 2
BNE x2, x0, selOutOrC_invsel
BN.ADDC w3, w3, w3 << 16B
LOOP x30, 10
BN.WSRRS w3, 1, w31
BN.WSRRS w2, 1, w31
BN.LID x9, 0(x21)
BN.SID x11, 0(x21)
BN.MOVR x11, x8++
BN.WSRRS w0, 1, w31
BN.MOV w0, w2
BN.WSRRS w2, 1, w31
BN.SEL w2, w0, w3, L
BN.SID x11, 0(x21++)
JALR x0, x1, 0
ADDI x0, x0, 0

selOutOrC_invsel:
BN.ADDC w3, w3, w3 << 16B
LOOP x30, 10
BN.WSRRS w3, 1, w31
BN.WSRRS w2, 1, w31
BN.LID x9, 0(x21)
BN.SID x11, 0(x21)
BN.MOVR x11, x8++
BN.WSRRS w0, 1, w31
BN.MOV w0, w2
BN.WSRRS w2, 1, w31
BN.SEL w2, w3, w0, L
BN.SID x11, 0(x21++)
JALR x0, x1, 0

modexp:
JAL x1, mulx
LW x16, 96(x0)
LW x17, 100(x0)
LW x18, 104(x0)
LW x19, 108(x0)
LW x20, 112(x0)
LW x21, 116(x0)
LW x22, 120(x0)
LW x23, 124(x0)
BN.SUB w2, w2, w2
LOOP x30, 4
ADDI x0, x0, 0
BN.LID x11, 0(x16++)
BN.SUBB w2, w31, w2
BN.SID x11, 0(x21++)
ADDI x0, x0, 0
SLLI x24, x22, 8
LOOP x24, 19
JAL x1, sqrx_exp
JAL x1, mulx_exp
LW x16, 96(x0)
LW x17, 100(x0)
LW x18, 104(x0)
LW x19, 108(x0)
LW x20, 112(x0)
LW x21, 116(x0)
LW x22, 120(x0)
LW x23, 124(x0)
BN.WSRRS w2, 1, w31
BN.ADD w2, w2, w2
LOOP x30, 4
BN.WSRRS w2, 1, w31
BN.LID x11, 0(x20)
BN.ADDC w2, w2, w2
BN.SID x11, 0(x20++)
JAL x1, selOutOrC
ADDI x0, x0, 0
ADDI x3, x0, 0
BN.LID x3, 96(x0)
LW x16, 96(x0)
LW x17, 100(x0)
LW x18, 104(x0)
LW x19, 108(x0)
LW x20, 112(x0)
LW x21, 116(x0)
LW x22, 120(x0)
LW x23, 124(x0)
JAL x1, mul1_exp
ECALL

modload:
BN.XOR w31, w31, w31
ADDI x3, x0, 0
BN.LID x3, 0(x0)
LW x16, 0(x0)
LW x17, 4(x0)
LW x18, 8(x0)
LW x19, 12(x0)
LW x20, 16(x0)
LW x21, 20(x0)
LW x22, 24(x0)
LW x23, 28(x0)
LW x24, 0(x0)
LW x25, 4(x0)
LW x26, 8(x0)
LW x27, 12(x0)
LW x28, 16(x0)
LW x29, 20(x0)
LW x30, 24(x0)
LW x31, 28(x0)
ADDI x8, x0, 28
ADDI x9, x0, 29
LW x10, 8(x0)
LW x11, 12(x0)
LW x12, 16(x0)
LW x13, 20(x0)
LW x14, 24(x0)
LW x15, 28(x0)
BN.LID x8, 0(x16)
JAL x1, d0inv
BN.SID x9, 0(x17)
JAL x1, computeRR
ECALL
