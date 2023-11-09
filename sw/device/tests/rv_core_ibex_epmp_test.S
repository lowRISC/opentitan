// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/sram_start.h"

  /**
   * The User Mode test function.
   *
   * This will be the only area, other than test location(s),
   * that will be executable by the user.
   *
   * An `ecall` is used to ask the Machine Mode to finish the test.
   */
  .balign 4
  .global i_am_become_user
  .type i_am_become_user, @function
i_am_become_user:
  la t0, test_locations
  addi t1, t0, 4 * 4 // test_location + (4 * kNumLocations)
1:
  lw t2, 0(t0)
  sw t2, 0(t0)
  jalr   0(t0)

  // The address to return to after an expected
  // instruction access fault has occurred.
  .global kExpUInstrAccFaultRet
kExpUInstrAccFaultRet:
  add t0, t0, 4
  blt t0, t1, 1b

  // Calls machine mode to finish the test.
  ecall
  .size i_am_become_user, .-i_am_become_user

  /**
   * The address past the end of the `i_am_become_user` function.
   */
  .balign 4
  .global kIAmBecomeUserEnd
kIAmBecomeUserEnd:

  /**
   * Finishes SRAM execution, indicating a successful run.
   *
   * Sets the stack pointer to a magic number
   * to indicate execution finished successfully.
   */
  .balign 4
  .global finish_test
  .type finish_test, @function
finish_test:
  li  sp, SRAM_MAGIC_SP_EXECUTION_DONE
  ebreak
  .size finish_test, .-finish_test
