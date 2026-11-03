# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Dummy instructions must not be counted in minstret.
#
# minstret is read around a csrr and eight nops, so the two reads differ by
# nine, with dummy instructions off, on at the highest rate (mask 0) and off
# again. The cosim checks the read values too.

#include "riscv_test.h"
#include "test_macros.h"

# cpuctrlsts (0x7c0): bit 2 dummy_instr_en, bits 5:3 dummy_instr_mask.
#define CPUCTRLSTS 0x7c0
#define CPUCTRLSTS_DUMMY_INSTR_EN 0x4

.macro CHECK_MINSTRET_DELTA idx
  li   gp, \idx
  csrr t0, minstret
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  csrr t1, minstret
  sub  t2, t1, t0
  li   t3, 9
  bne  t2, t3, fail
.endm

RVTEST_RV32M
RVTEST_CODE_BEGIN

  # Baseline with dummy instructions disabled.
  CHECK_MINSTRET_DELTA 1

  # Enable dummy instruction insertion at the highest rate and repeat the
  # measurement; the insertion points walk across the window.
  csrsi CPUCTRLSTS, CPUCTRLSTS_DUMMY_INSTR_EN
  li   t4, 32
1:
  CHECK_MINSTRET_DELTA 2
  addi t4, t4, -1
  bnez t4, 1b

  # Disable again and re-check the baseline.
  csrci CPUCTRLSTS, CPUCTRLSTS_DUMMY_INSTR_EN
  CHECK_MINSTRET_DELTA 3

  j    pass

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
