// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Flash executable runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section 
  // is allocated space in ROM by the linker.
  .section .crt, "ax"

  .extern main

/**
 * Callable entry point for flash.
 *
 * This sets up the stack, zeroes |.bss|, and sets up |.data|.
 * It then jumps into main.
 */
_start:
  .globl _start

  // Set up the stack. We have no expectation that the rom that
  // jumps here will have the correct stack start linked in.
  la sp, _stack_start

  // Set up the new interrupt vector.
  la   t0, _vectors_start
  csrw mtvec, t0

  // Zero out the |.bss| segment.
  //
  // We use |t0| and |t1| to represent the start and end pointers
  // of |.bss|.
  la  t0, _bss_start
  la  t1, _bss_end
  bge t0, t1, bss_zero_loop_end
bss_zero_loop:
  sw    zero, 0(t0)
  addi  t0, t0, 0x4
  ble   t0, t1, bss_zero_loop
bss_zero_loop_end:

  // Initialize the |.data| segment from the |.idata| segment.
  //
  // We use |t0| and |t1| to represent the start and end pointers
  // of |.data|, |t2| to represent the start pointer of |.idata|
  // (which has the same length as |.data|) and |t3| is a scratch
  // register for the copy.
  la  t0, _data_start
  la  t1, _data_end
  la  t2, _data_init_start
  bge t0, t1, data_copy_loop_end
data_copy_loop:
  lw   t3, 0(t2)
  sw   t3, 0(t0)
  addi t0, t0, 0x4
  addi t2, t2, 0x4
  ble  t0, t1, data_copy_loop
data_copy_loop_end:

  // Jump into the C program entry point. This is your standard
  // C |main()|, so we need to pass dummy values for |argc| and |argv|.
  li   a0, 0x0  // argc = 0
  li   a1, 0x0  // argv = NULL
  call main

  // Loop forever if main somehow returns.
1:
  wfi
  j 1b
