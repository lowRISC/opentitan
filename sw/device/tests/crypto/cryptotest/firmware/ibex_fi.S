// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Increments a value 100 times by 1.
 *
 * @param a0 initial value which gets incremented.
 */
  .globl target_function
  .type target_function, @function
  .balign 256
target_function:
  // a0: init value
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  addi a0, a0, 1
  ret


/**
 * Increments a value 100 times by 10.
 *
 * @param a0 initial value which gets incremented.
 */
  .globl expected_function
  .type expected_function, @function
  .balign 256
expected_function:
  // a0: init value
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  addi a0, a0, 10
  ret
