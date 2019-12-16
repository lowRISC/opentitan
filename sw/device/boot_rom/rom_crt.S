// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Boot ROM runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section 
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

/**
 * Entry point after reset. This symbol is jumped to from the handler 
 * for IRQ 0x80.
 *
 * Sets up the stack, then jumps to |_start|.
 */
_reset_start:
  .globl _reset_start
  // Clobber all writeable registers.
  li  x1, 0x0
  li  x2, 0x0
  li  x3, 0x0
  li  x4, 0x0
  li  x5, 0x0
  li  x6, 0x0
  li  x7, 0x0
  li  x8, 0x0
  li  x9, 0x0
  li  x10, 0x0
  li  x11, 0x0
  li  x12, 0x0
  li  x13, 0x0
  li  x14, 0x0
  li  x15, 0x0
  li  x16, 0x0
  li  x17, 0x0
  li  x18, 0x0
  li  x19, 0x0
  li  x20, 0x0
  li  x21, 0x0
  li  x22, 0x0
  li  x23, 0x0
  li  x24, 0x0
  li  x25, 0x0
  li  x26, 0x0
  li  x27, 0x0
  li  x28, 0x0
  li  x29, 0x0
  li  x30, 0x0
  li  x31, 0x0

  // Set up the stack.
  la  sp, _stack_start

  // Explicit fall-through to |_start|.

/**
 * Callable entry point for the boot rom.
 *
 * Currently, this zeroes the |.bss| section, copies initial data to
 * |.data|, and then jumps to the program entry point.
 */
_start:
  .globl _start

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

  // Re-clobber all of the registers from above.
  li t0, 0x0
  li t1, 0x0
  li t2, 0x0
  li t3, 0x0

  // Jump into the C program entry point.
  call _boot_start
  
  // Loop forever if _boot_start somehow returns.
1:
  wfi
  j 1b
