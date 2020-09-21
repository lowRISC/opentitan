// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Flash executable runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated space in ROM by the linker.
  .section .crt, "ax", @progbits

  .extern main
  .extern crt_interrupt_vector
  .extern kDeviceStopAddress

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
  la sp, _stack_start

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
  //
  // We use `t0` and `t1` to represent the start and end pointers
  // of `.bss`.
  la   t0, _bss_start
  la   t1, _bss_end
  bgeu t0, t1, bss_zero_loop_end
bss_zero_loop:
  sw    zero, 0(t0)
  addi  t0, t0, 0x4
  bltu  t0, t1, bss_zero_loop
bss_zero_loop_end:

  // Zero out the stack
  //
  // We use `t0` and `t1` to represent the start and end pointers of the stack.
  // As the stack grows downwards and we zero going forwards the start pointer
  // starts as _stack_end and the end pointer at _stack_start.
  la   t0, _stack_end
  la   t1, _stack_start
  bgeu t0, t1, stack_zero_loop_end
stack_zero_loop:
  sw    zero, 0(t0)
  addi  t0, t0, 0x4
  bltu  t0, t1, stack_zero_loop
stack_zero_loop_end:

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

  // Load `kDeviceStopAddress` into `t0`. If it is non-zero, write the return
  // value from `main` (in `a0`) into it, otherwise, skip to `wfi` loop.
  lw t0, kDeviceStopAddress
  beqz t0, wfi_loop
  sw a0, 0(t0)

  // Loop forever if main somehow returns.
wfi_loop:
  wfi
  j wfi_loop
