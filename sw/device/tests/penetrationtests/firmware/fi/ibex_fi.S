// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Increments a value 100 times by 1.
 *
 * As this function is targeted by fault injection, the code is unrolled.
 *
 * @param a0 initial value which gets incremented.
 * @return Initial value incremeted 100 times by 1.
 */
  .globl increment_100x1
  .type increment_100x1, @function
  .balign 256
increment_100x1:
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
 * As this function is targeted by fault injection, the code is unrolled.
 *
 * @param a0 initial value which gets incremented.
 * @return Initial value incremeted 100 times by 10.
 */
  .globl increment_100x10
  .type increment_100x10, @function
  .balign 256
increment_100x10:
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
