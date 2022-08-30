// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * OTTF Interrupt Vector.
 */

  .section .vectors, "ax"
  .option push

  // Disable RISC-V instruction compression: we need all instructions to
  // be exactly word wide in the interrupt vector.
  .option norvc

  // Disable RISC-V linker relaxation, as it can compress instructions at
  // link-time, which we also really don't want.
  .option norelax

  /**
   * `_ottf_interrupt_vector` is an ibex-compatible interrupt vector.
   *
   * Interrupt vectors in Ibex have 32 4-byte entries for 32 possible interrupts.
   * The vector must be 256-byte aligned, as Ibex's vectoring mechanism requires
   * that.
   *
   * Only the following will be used by Ibex:
   * - Exception Handler (Entry 0)
   * - Machine Software Interrupt Handler (Entry 3)
   * - Machine Timer Interrupt Handler (Entry 7)
   * - Machine External Interrupt Handler (Entry 11)
   * - Vendor Interrupt Handlers (Entries 16-31)
   *
   * More information about Ibex's interrupts can be found here:
   *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
   */
  .balign 256
  .global _ottf_interrupt_vector
  .type _ottf_interrupt_vector, @function
_ottf_interrupt_vector:
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
  j handler_irq_internal

  // Set size so vector can be disassembled.
  .size _ottf_interrupt_vector, .-_ottf_interrupt_vector

  .option pop

// -----------------------------------------------------------------------------

/**
 * OTTF runtime initialization code.
 */

  /**
   * NOTE: The "ax" flag below is necessary to ensure that this section
   * is allocated executable space in ROM by the linker.
   */
  .section .crt, "ax"

  /**
   * Entry point.
   *
   * This symbol is jumped to from the test ROM or ROM using the
   * `entry_point` field of the manifest.
   */
  .balign 4
  .global _ottf_start
  .type _ottf_start, @function
_ottf_start:
  /**
   * Set up the global pointer `gp`.
   *
   * Linker relaxations are disabled until the global pointer is setup below,
   * because otherwise some sequences may be turned into `gp`-relative
   * sequences, which is incorrect when `gp` is not initialized.
   */
  .option push
  .option norelax
  la gp, __global_pointer$
  .option pop

  /**
   * Set up the stack pointer.
   *
   * In RISC-V, the stack grows downwards, so we load the address of the highest
   * word in the stack into sp. We don't load in `_stack_end`, as that points
   * beyond the end of RAM, and we always want it to be valid to dereference
   * `sp`, and we need this to be 128-bit (16-byte) aligned to meet the psABI.
   *
   * If an exception fires, the handler is conventionaly only allowed to clobber
   * memory at addresses below `sp`.
   */
  la   sp, (_stack_end - 16)

  /**
   * Set well-defined interrupt/exception handlers.
   *
   * The lowest two bits should be `0b01` to ensure we use vectored interrupts.
   */
  la   t0, (_ottf_interrupt_vector + 1)
  csrw mtvec, t0

  /**
   * Setup C Runtime
   */

  /**
   * Initialize the `.data` section in RAM from Flash.
   */
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  call crt_section_copy

  /**
   * Initialize the `.bss` section.
   *
   * We do this despite zeroing all of SRAM above, so that we still zero `.bss`
   * once we've enabled SRAM scrambling.
   */
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

 /**
  * Call the functions in the `.init_array` section.
  *
  * This section is typically empty except for executables built with LLVM
  * coverage enabled. When coverage is enabled, the compiler emits pointers to
  * the functions that initialize the profile buffer in this section. These
  * functions must be called before the instrumented functions in the program.
  *
  * We use `s0` and `s1` to represent the start and end pointers of
  * `.init_array`, respectively, and `t0` to store the addresses of the
  * functions to be called.
  */
  la   s0, _init_array_start
  la   s1, _init_array_end
  bgeu s0, s1, init_array_loop_end
init_array_loop:
  lw   t0, 0(s0)
  jalr t0
  addi s0, s0, 0x4
  bltu s0, s1, init_array_loop
init_array_loop_end:

 /**
  * Jump into the OTTF C entry point.
  */
  tail _ottf_main
  .size _ottf_start, .-_ottf_start
