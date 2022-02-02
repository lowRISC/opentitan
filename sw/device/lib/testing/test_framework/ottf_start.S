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
 * Ibex-specific interrupt vectors for test flash images.
 *
 * This is similar to the test ROM interrupt vectors configured in the Test ROM
 * (`sw/device/lib/testing/test_rom/test_rom_start.S`), except these are placed
 * in flash, and point to the OTTF ISRs declared in
 * `sw/device/lib/testing/test_framework/ottf_isrs.S`. If you are getting link
 * errors for these symbols, then it's likely you have forgotten to add
 * `ottf_isrs` as a dependency for your executable.
 */

  // These symbols are declared in
  // `sw/device/lib/testing/test_framework/ottf_isrs.S`.
  .extern handler_exception
  .extern handler_irq_software
  .extern handler_irq_timer
  .extern handler_irq_external

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated space in flash by the linker.
  .section .vectors, "ax"
  .option push
  // Switch off compressed instructions so we know each instruction below is
  // exactly 4 bytes (one entry).
  .option norvc
  // Switch off linker relaxation so that the linker does not reduce the size of
  // any entries.
  .option norelax

  .balign 256
  .global _interrupt_vector
  .type _interrupt_vector, @function
_interrupt_vector:

  // RISC-V Standard (Vectored) Interrupt Handlers:

  // Exception and User Software Interrupt Handler.
  j handler_exception
  // Supervisor Software Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Software Interrupt Handler.
  j handler_irq_software

  // User Timer Interrupt Handler.
  unimp
  // Supervisor Timer Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Timer Interrupt Handler.
  j handler_irq_timer

  // User External Interrupt Handler.
  unimp
  // Supervisor External Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine External Interrupt Handler.
  j handler_irq_external

  // Reserved.
  unimp
  unimp
  unimp
  unimp

  // Vendor Interrupt Handlers:

  // On Ibex, interrupt IDs 16-30 are for "fast" interrupts.
  .rept 15
  unimp
  .endr

  // On Ibex, interrupt ID 31 is for non-maskable interrupts
  unimp

  // Set size so vector can be disassembled.
  .size _interrupt_vector, .-_interrupt_vector

  .option pop

/**
 * Flash executable runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated space in ROM by the linker.
  .section .crt, "ax", @progbits

/**
 * Callable entry point for flash.
 *
 * This sets up the stack, zeroes `.bss`, and sets up `.data`.
 * It then jumps into main.
 */
  .globl _start
  .type _start, @function
_start:

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
  la   t0, (_interrupt_vector + 1)
  csrw mtvec, t0

  // Zero out the `.bss` segment.
  la   a0, _bss_start
  la   a1, _bss_end
  .extern crt_section_clear
  call crt_section_clear

  // Initialize the `.data` segment from the `.idata` segment.
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  .extern crt_section_copy
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

  // Jump into the OTTF C entry point. This is your standard C `main()`, so we
  // need to pass dummy values for `argc` and `argv`.
  li   a0, 0x0  // argc = 0
  li   a1, 0x0  // argv = NULL
  .extern main
  tail main

  // Set size so this function can be disassembled.
  .size _start, .-_start
