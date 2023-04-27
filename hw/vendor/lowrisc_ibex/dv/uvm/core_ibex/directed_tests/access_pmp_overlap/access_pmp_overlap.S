# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

###############################################################################
# Description:
#   Test to access misalign address between a PMP
# and a non-PMP region. PMP region allows access
# so the purpose is to check the implementation
# behavior of multiple accesses.

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  # setting machine handler
  la   t0, mtvec_handler
  csrw mtvec, t0

  # setting the PMP region
  la   t0, pmp_region_start
  srli t1, t0, PMP_SHIFT
  csrw pmpaddr0, t1
  la   t1, pmp_region_end
  srli t1, t1, PMP_SHIFT
  csrw pmpaddr1, t1
  li   t1, (PMP_L | PMP_TOR | PMP_R | PMP_W | PMP_X) << 8
  csrw pmpcfg0, t1

  # access across the boundary between PMP and non-PMP
  lw   t1, -2(t0)

  j pass

  TEST_PASSFAIL

.balign 256
mtvec_handler:
  j fail

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

.balign 0x1000
pmp_region_start: .zero 0x1000
pmp_region_end:
  TEST_DATA

RVTEST_DATA_END
