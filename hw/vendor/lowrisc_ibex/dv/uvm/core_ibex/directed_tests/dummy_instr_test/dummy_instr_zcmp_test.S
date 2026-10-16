# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Dummy instructions must not disturb an expanded Zcmp sequence.
#
# A round runs cm.push/cm.pop with the full register list, cm.mvsa01,
# cm.mva01s, and cm.popret/cm.popretz through a call, and checks the frame,
# sp, the registers and the returns. It runs once with dummy instructions off,
# then 48 times with them at the highest rate (mask 0), so a dummy falls due
# before every kind of uop and has to wait. A lost uop leaves a canary, a stale
# register, a wrong sp or a fall-through past the return.
#
# dummy_instr_zcmp_debug_test and dummy_instr_zcmp_irq_test run this program
# under random debug requests or interrupts, whose handlers only return. A
# restarted cm.popret leaves a wrong sp or returns to a bad address.
#
# The encodings are raw halfwords because the pinned toolchain has no Zcmp.
# Cosim mismatches are not fatal: the cosim does not enable Zcmp.

#include "riscv_test.h"
#include "test_macros.h"

# cpuctrlsts (0x7c0): bit 2 dummy_instr_en, bits 5:3 dummy_instr_mask.
#define CPUCTRLSTS 0x7c0
#define CPUCTRLSTS_DUMMY_INSTR_EN 0x4

#define CANARY 0xdeadbeef

# mie: fast interrupts 0-14, external, timer and software.
#define MIE_ALL 0x7fff0888

# Register use:
#   gp (TESTNUM) index of the round in progress, for the failure trace
#   t4           round counter for the loop with dummies enabled
#   t0, t1       scratch inside a round
# ra and s0-s11 are the pushed/popped registers, a0/a1 and s0-s3 the moved ones.

# The frame of cm.push {ra, s0-s11}, -64 is 64 bytes. The registers are stored
# from the top of the frame downwards in the order s11, s10 ... s0, ra (Zc spec
# 1.0, cm.push): s11 at 60(sp), s10 at 56(sp) ... s0 at 16(sp), ra at 12(sp).
# 0(sp)..8(sp) is padding the sequence must not write.
.macro CHECK_SLOT offset, reg
  lw   t0, \offset(sp)
  bne  t0, \reg, fail
.endm

.macro CHECK_CANARY offset
  lw   t0, \offset(sp)
  li   t1, CANARY
  bne  t0, t1, fail
.endm

.macro CHECK_REG reg, value
  li   t0, \value
  bne  t0, \reg, fail
.endm

.macro ZCMP_ROUND idx
  li   gp, \idx

  # Fill the frame with a canary and give every pushed register a distinct value.
  la   sp, stack_top
  li   t0, CANARY
  sw   t0, -4(sp)
  sw   t0, -8(sp)
  sw   t0, -12(sp)
  sw   t0, -16(sp)
  sw   t0, -20(sp)
  sw   t0, -24(sp)
  sw   t0, -28(sp)
  sw   t0, -32(sp)
  sw   t0, -36(sp)
  sw   t0, -40(sp)
  sw   t0, -44(sp)
  sw   t0, -48(sp)
  sw   t0, -52(sp)
  sw   t0, -56(sp)
  sw   t0, -60(sp)
  sw   t0, -64(sp)
  li   ra,  0x1a000000 + \idx
  li   s0,  0x50000000 + \idx
  li   s1,  0x51000000 + \idx
  li   s2,  0x52000000 + \idx
  li   s3,  0x53000000 + \idx
  li   s4,  0x54000000 + \idx
  li   s5,  0x55000000 + \idx
  li   s6,  0x56000000 + \idx
  li   s7,  0x57000000 + \idx
  li   s8,  0x58000000 + \idx
  li   s9,  0x59000000 + \idx
  li   s10, 0x5a000000 + \idx
  li   s11, 0x5b000000 + \idx

  .2byte 0xb8f2                 # cm.push {ra, s0-s11}, -64

  la   t0, stack_top
  addi t0, t0, -64
  bne  t0, sp, fail
  CHECK_SLOT 60, s11
  CHECK_SLOT 56, s10
  CHECK_SLOT 52, s9
  CHECK_SLOT 48, s8
  CHECK_SLOT 44, s7
  CHECK_SLOT 40, s6
  CHECK_SLOT 36, s5
  CHECK_SLOT 32, s4
  CHECK_SLOT 28, s3
  CHECK_SLOT 24, s2
  CHECK_SLOT 20, s1
  CHECK_SLOT 16, s0
  CHECK_SLOT 12, ra
  CHECK_CANARY 8
  CHECK_CANARY 4
  CHECK_CANARY 0

  # Clobber everything the pop must restore.
  li   ra,  0
  li   s0,  0
  li   s1,  0
  li   s2,  0
  li   s3,  0
  li   s4,  0
  li   s5,  0
  li   s6,  0
  li   s7,  0
  li   s8,  0
  li   s9,  0
  li   s10, 0
  li   s11, 0

  .2byte 0xbaf2                 # cm.pop {ra, s0-s11}, 64

  la   t0, stack_top
  bne  t0, sp, fail
  CHECK_REG ra,  0x1a000000 + \idx
  CHECK_REG s0,  0x50000000 + \idx
  CHECK_REG s1,  0x51000000 + \idx
  CHECK_REG s2,  0x52000000 + \idx
  CHECK_REG s3,  0x53000000 + \idx
  CHECK_REG s4,  0x54000000 + \idx
  CHECK_REG s5,  0x55000000 + \idx
  CHECK_REG s6,  0x56000000 + \idx
  CHECK_REG s7,  0x57000000 + \idx
  CHECK_REG s8,  0x58000000 + \idx
  CHECK_REG s9,  0x59000000 + \idx
  CHECK_REG s10, 0x5a000000 + \idx
  CHECK_REG s11, 0x5b000000 + \idx

  # cm.mvsa01 s0, s1: s0 = a0, s1 = a1.
  li   a0, 0xa0a0a0a0
  li   a1, 0xa1a1a1a1
  li   s0, 0
  li   s1, 0
  .2byte 0xac26                 # cm.mvsa01 s0, s1
  bne  s0, a0, fail
  bne  s1, a1, fail

  # cm.mva01s s2, s3: a0 = s2, a1 = s3.
  li   s2, 0x52525252
  li   s3, 0x53535353
  li   a0, 0
  li   a1, 0
  .2byte 0xad6e                 # cm.mva01s s2, s3
  bne  a0, s2, fail
  bne  a1, s3, fail

  # cm.popret and cm.popretz through a call: the return must happen, a0 must
  # carry the callee's value (or zero), and sp must be back where it started.
  li   a0, 0
  jal  ra, popret_sub
  li   t0, 0x55
  bne  t0, a0, fail
  la   t0, stack_top
  bne  t0, sp, fail

  li   a0, 0
  jal  ra, popretz_sub
  bnez a0, fail
  la   t0, stack_top
  bne  t0, sp, fail
.endm

# Debug entry: DmHaltAddr is the start of .text.init. Resume at once. The
# reset code of RVTEST_CODE_BEGIN starts at offset 0x80.
  .section .text.init
  dret

RVTEST_RV32M
RVTEST_CODE_BEGIN

  la   t0, irq_vector
  csrw mtvec, t0
  li   t0, MIE_ALL
  csrw mie, t0
  csrsi mstatus, MSTATUS_MIE

  # Baseline with dummy instructions disabled.
  ZCMP_ROUND 1

  # Enable dummy instruction insertion at the highest rate and repeat.
  csrsi CPUCTRLSTS, CPUCTRLSTS_DUMMY_INSTR_EN
  li   t4, 48
1:
  ZCMP_ROUND 2
  addi t4, t4, -1
  bnez t4, 1b

  csrci CPUCTRLSTS, CPUCTRLSTS_DUMMY_INSTR_EN
  j    pass

  TEST_PASSFAIL

  # The jump after each cm.popret/cm.popretz is only reached if the return
  # micro-op was dropped.
  .balign 4
popret_sub:
  .2byte 0xb842                 # cm.push {ra}, -16
  li   a0, 0x55
  .2byte 0xbe42                 # cm.popret {ra}, 16
  j    fail

  .balign 4
popretz_sub:
  .2byte 0xb842                 # cm.push {ra}, -16
  li   a0, 0x55
  .2byte 0xbc42                 # cm.popretz {ra}, 16
  j    fail

  # Vectored mtvec: exceptions (none are expected) at the base, interrupt n at
  # base + 4n. The testbench drops each interrupt line on its own.
  .balign 256
irq_vector:
  .option push
  .option norvc
  j    fail
  .rept 31
  mret
  .endr
  .option pop

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
  .balign 16
stack_bot:
  .fill 32, 4, 0
stack_top:
  .fill 4, 4, 0
RVTEST_DATA_END
