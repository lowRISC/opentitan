# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Tests U-mode execution across all of the locked non-MML PMP permission
# configurations

#include "riscv_test.h"
#include "test_macros.h"
#include "custom_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN
  RESET_PMP
  # Setup region that can be fully accessed by U mode
  SET_PMP_NAPOT(test_code, 4096, PMP_R | PMP_W | PMP_X, 15)

  # Setup exception handler
  la   t0, mtvec_handler
  csrw mtvec, t0

  j test_code

test_end:
  j pass

  TEST_PASSFAIL

.balign 4096
test_code:
  # As we cannot modify locked regions setup new regions with increase priority
  # (lower numbered regions take priority). Run a U-mode execution after every
  # every new region to setup to test its configuration before moving to the
  # next.
  SET_PMP_NAPOT(test_exec_region, 256, PMP_NAPOT, 14)
  SWITCH_TO_U_MODE_LABEL(test_exec_region)
  SET_PMP_NAPOT(test_exec_region, 256, PMP_L | PMP_NAPOT, 13)
  SWITCH_TO_U_MODE_LABEL(test_exec_region)
  SET_PMP_NAPOT(test_exec_region, 256, PMP_L | PMP_R| PMP_NAPOT, 12)
  SWITCH_TO_U_MODE_LABEL(test_exec_region)
  SET_PMP_NAPOT(test_exec_region, 256, PMP_L | PMP_R | PMP_W| PMP_NAPOT, 11)
  SWITCH_TO_U_MODE_LABEL(test_exec_region)
  SET_PMP_NAPOT(test_exec_region, 256, PMP_L | PMP_X | PMP_R | PMP_W | PMP_NAPOT, 10)
  SWITCH_TO_U_MODE_LABEL(test_exec_region)
  SET_PMP_NAPOT(test_exec_region, 256, PMP_L | PMP_X | PMP_R | PMP_NAPOT, 9)
  SWITCH_TO_U_MODE_LABEL(test_exec_region)
  SET_PMP_NAPOT(test_exec_region, 256, PMP_L | PMP_X | PMP_NAPOT, 8)
  SWITCH_TO_U_MODE_LABEL(test_exec_region)

  j test_end

.balign 256
test_exec_region:
  add t0, t0, t0
  # Jump to exception handler to return to M-mode where U mode exec succeeds
  unimp

.balign 256
mtvec_handler:
  csrw mepc, a0
  # always return to m-mode
  li t0, MSTATUS_MPP
  csrs mstatus, t0
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
