# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This test verifies the mcounteren write-lock mechanism by dynamically setting
# the mcounteren_writable_i hardware input. It validates that register updates
# are silently ignored while locked and succeed when unlocked, using immediate
# software readbacks to confirm the state. Inter-process signaling with the UVM
# testbench is achieved by monitoring writes to mcycle (lock command) and
# mcycleh (unlock command).

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32M
RVTEST_CODE_BEGIN

  # Initial Write (Unlocked)
  li   s0, 0x5
  csrw mcounteren, s0
  csrr t1, mcounteren
  li   t2, 0x5
  # If readback != 0x5, fail immediately
  bne  t1, t2, fail

  # Tell UVM to lock by writing to mcycle, which is monitored by the UVM
  # testbench to set `mcounteren_writable`
  csrw mcycle, x0

  # Small delay loop to let the hardware pin force propagate
  .rept 5
  nop
  .endr

  # Try to overwrite mcounteren with 0x0 while locked
  li   s1, 0x0
  csrw mcounteren, s1
  csrr t1, mcounteren
  bne  t1, s0, fail

  # Tell UVM to unlock by writing to mcycleh
  csrw mcycleh, x0

  .rept 5
  nop
  .endr

  # Try to overwrite it with 0x0 again. This time while unlocked
  li   s3, 0x0
  csrw mcounteren, s3
  csrr t1, mcounteren
  bne  t1, s3, fail

  # Success Exit
  j    pass
  TEST_PASSFAIL

RVTEST_CODE_END

RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
