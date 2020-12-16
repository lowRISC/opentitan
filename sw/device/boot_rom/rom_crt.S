// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Boot ROM runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  .extern crt_section_clear
  .extern crt_section_copy

/**
 * Entry point after reset. This symbol is jumped to from the handler
 * for IRQ 0x80.
 *
 * Sets up the stack, then jumps to `_start`.
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
  la  sp, _stack_end

  // Set up the global pointer. This requires that we disable linker relaxations
  // (or it will be relaxed to `mv gp, gp`).
  .option push
  .option norelax
  la  gp, __global_pointer$
  .option pop

  // Explicit fall-through to `_start`.

/**
 * Callable entry point for the boot rom.
 *
 * Currently, this zeroes the `.bss` section, copies initial data to
 * `.data`, and then jumps to the program entry point.
 */
_start:
  .globl _start

  // Zero out the `.bss` segment.
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

  // Zero out the stack
  //
  // As the stack grows downwards and we zero going forwards the start pointer
  // starts as _stack_start and the end pointer at _stack_end.
  la   a0, _stack_start
  la   a1, _stack_end
  call crt_section_clear

  // Initialize the `.data` segment from the `.idata` segment.
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  call crt_section_copy

  // Clobber all temporary registers.
  li t0, 0x0
  li t1, 0x0
  li t2, 0x0
  li t3, 0x0
  li t4, 0x0
  li t5, 0x0
  li t6, 0x0

  // Clobber all argument registers.
  li a0, 0x0
  li a1, 0x0
  li a2, 0x0
  li a3, 0x0
  li a4, 0x0
  li a5, 0x0
  li a6, 0x0
  li a7, 0x0

  // Jump into the C program entry point.
  call _boot_start

  // Loop forever if _boot_start somehow returns.
1:
  wfi
  j 1b
