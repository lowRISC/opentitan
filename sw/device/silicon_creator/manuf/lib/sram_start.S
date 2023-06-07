// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sram_start.h"

/**
 * CRT library for SRAM programs.
 *
 * The purpose of this small library is to setup the stack pointer, global
 * pointer and verify the integrity
 */

  .section .sram_start, "ax"

  .balign 4
  .global sram_start
  .type sram_start, @function
sram_start:

  // Set up the global pointer. This requires that we disable linker relaxations
  // (or it will be relaxed to `mv gp, gp`).
  .option push
  .option norelax
  la  gp, __global_pointer$
  .option pop

  // Set up the stack.
  la  sp, _stack_end

  // Zero out the `.bss` segment.
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

  // Jump into the C program entry point.
  call sram_main

  // Notify the host that we are done.
  li  sp, SRAM_MAGIC_SP_EXECUTION_DONE
  ebreak

  // Set function size to allow disassembly.
  .size sram_start, .-sram_start
