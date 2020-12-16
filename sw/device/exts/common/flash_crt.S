// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Flash header.
 *
 * Contains the address of the entry point.
 */
  .section .flash_header, "a", @progbits
  .4byte _start

/**
 * Flash executable runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated space in ROM by the linker.
  .section .crt, "ax", @progbits

  .extern abort
  .extern main
  .extern crt_interrupt_vector
  .extern crt_section_clear
  .extern crt_section_copy

/**
 * Callable entry point for flash.
 *
 * This sets up the stack, zeroes `.bss`, and sets up `.data`.
 * It then jumps into main.
 */
_start:
  .globl _start

  // Set up the stack. We have no expectation that the rom that
  // jumps here will have the correct stack start linked in.
  la sp, _stack_end

  // Set up the global pointer. This requires that we disable linker relaxations
  // (or it will be relaxed to `mv gp, gp`).
  .option push
  .option norelax
  la gp, __global_pointer$
  .option pop

  // Set up the new interrupt vector.
  la   t0, crt_interrupt_vector
  csrw mtvec, t0

  // Zero out the `.bss` segment.
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

  // Zero out the stack
  la   a0, _stack_start
  la   a1, _stack_end
  call crt_section_clear

  // Initialize the `.data` segment from the `.idata` segment.
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  call crt_section_copy

  // Call the functions in the `.init_array` section.
  //
  // This section is typically empty except for executables built with LLVM
  // coverage enabled. When coverage is enabled, the compiler emits pointers to
  // the functions that initialize the profile buffer in this section. These
  // functions must be called before the instrumented functions in the program.
  //
  // We use `s0` and `s1` to represent the start and end pointers of
  // `.init_array`, respectively, and `t0` to store the addresses of the
  // functions to be called.
  la   s0, _init_array_start
  la   s1, _init_array_end
  bgeu s0, s1, init_array_loop_end
init_array_loop:
  lw   t0, 0(s0)
  jalr t0
  addi s0, s0, 0x4
  bltu s0, s1, init_array_loop
init_array_loop_end:

  // Jump into the C program entry point. This is your standard
  // C `main()`, so we need to pass dummy values for `argc` and `argv`.
  li   a0, 0x0  // argc = 0
  li   a1, 0x0  // argv = NULL
  call main

  // Halt the core (wfi loop)
  tail abort
