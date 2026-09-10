// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Stub ROM interrupt vectors.
 *
 * After reset all interrupts are disabled. Only exceptions (interrupt 0) and
 * non-maskable interrupts (interrupt 31) are possible. For simplicity however
 * we just set all interrupt handlers in the Stub ROM to use the same handler,
 * which loops forever.
 *
 * Interrupt vectors in Ibex have 32 entries for 32 possible interrupts. The
 * vector must be 256-byte aligned, as Ibex's vectoring mechanism requires that.
 *
 * Note that the Ibex reset handler (entry point) immediately follows this
 * interrupt vector and can be thought of as an extra entry.
 *
 * More information about Ibex's interrupts can be found here:
 *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
 */

  // Push Stub ROM interrupt vector options.
  .option push

  // Disable RISC-V instruction compression: we need all instructions to
  // be exactly word wide in the interrupt vector.
  .option norvc

  // Disable RISC-V linker relaxation, as it can compress instructions at
  // link-time, which we also really don't want.
  .option norelax

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .vectors, "ax"
  .balign 256
  .global _interrupt_vector
  .type _interrupt_vector, @function
_interrupt_vector:

  // Each jump instruction must be exactly 4 bytes in order to ensure that the
  // entries are properly located.
  .rept 32
  j _reset_start
  .endr

  // Ibex reset vector, the initial entry point after reset. (This falls at IRQ
  // handler 0x80.)
  j _reset_start

  // Set size so this vector can be disassembled.
  .size _interrupt_vector, .-_interrupt_vector

  // Pop ROM interrupt vector options.
  //
  // Re-enable compressed instructions, linker relaxation.
  .option pop

// -----------------------------------------------------------------------------

/**
 * Stub ROM runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  /**
   * Entry point after reset. This symbol is jumped to from the handler
   * for IRQ 0x80.
   */
  .balign 4
  .global _reset_start
  .type _reset_start, @function
_reset_start:
  wfi
  j   _reset_start

  .size _reset_start, .-_reset_start
