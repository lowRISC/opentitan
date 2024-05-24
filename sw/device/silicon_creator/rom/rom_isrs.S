// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"

// NOTE: The "ax" flag below is necessary to ensure that this section
// is allocated executable space in ROM by the linker.
.section .rom_isrs, "ax"

// -----------------------------------------------------------------------------

  /**
   * Compute the MEPC that will be saved to the stack by the associated ISR
   * handler sub-routine below.
   *
   * This subroutine is only invoked for IRQs that are synchronous. Specifically,
   * this subroutine updates the ISR return address to point to the instruction
   * after the trapped instruction to prevent an endless interrupt cycle.
   *
   * Since we support the RISC-V compressed instructions extension, we need to
   * check if the two least significant bits of the instruction are
   * b11 (0x3), which means that the trapped instruction is not compressed,
   * i.e., the trapped instruction is 32bits = 4bytes. Otherwise, the trapped
   * instruction is 16bits = 2bytes.
   */
  .balign 4
  .type rom_compute_mepc_on_synchronous_irq, @function
rom_compute_mepc_on_synchronous_irq:
  csrr t0, mepc
  lh t2, 0(t0)
  li t1, 0x3
  and t3, t2, t1
  beq t3, t1, .L_rom_32bit_trap_instr
  addi t0, t0, OT_HALF_WORD_SIZE
  ret
.L_rom_32bit_trap_instr:
  addi t0, t0, OT_WORD_SIZE
  ret
  .size rom_compute_mepc_on_synchronous_irq, .-rom_compute_mepc_on_synchronous_irq

// -----------------------------------------------------------------------------

  /**
   * Exception handler.
   */
  .balign 4
  .global rom_exception_handler_entry
  .type rom_exception_handler_entry, @function
rom_exception_handler_entry:
  // Save all registers to the stack.
  addi sp, sp, -OT_CONTEXT_SIZE
  sw   ra,  1 * OT_WORD_SIZE(sp)
  sw   t0,  2 * OT_WORD_SIZE(sp)
  sw   t1,  3 * OT_WORD_SIZE(sp)
  sw   t2,  4 * OT_WORD_SIZE(sp)
  sw   s0,  5 * OT_WORD_SIZE(sp)
  sw   s1,  6 * OT_WORD_SIZE(sp)
  sw   a0,  7 * OT_WORD_SIZE(sp)
  sw   a1,  8 * OT_WORD_SIZE(sp)
  sw   a2,  9 * OT_WORD_SIZE(sp)
  sw   a3, 10 * OT_WORD_SIZE(sp)
  sw   a4, 11 * OT_WORD_SIZE(sp)
  sw   a5, 12 * OT_WORD_SIZE(sp)
  sw   a6, 13 * OT_WORD_SIZE(sp)
  sw   a7, 14 * OT_WORD_SIZE(sp)
  sw   s2, 15 * OT_WORD_SIZE(sp)
  sw   s3, 16 * OT_WORD_SIZE(sp)
  sw   s4, 17 * OT_WORD_SIZE(sp)
  sw   s5, 18 * OT_WORD_SIZE(sp)
  sw   s6, 19 * OT_WORD_SIZE(sp)
  sw   s7, 20 * OT_WORD_SIZE(sp)
  sw   s8, 21 * OT_WORD_SIZE(sp)
  sw   s9, 22 * OT_WORD_SIZE(sp)
  sw  s10, 23 * OT_WORD_SIZE(sp)
  sw  s11, 24 * OT_WORD_SIZE(sp)
  sw   t3, 25 * OT_WORD_SIZE(sp)
  sw   t4, 26 * OT_WORD_SIZE(sp)
  sw   t5, 27 * OT_WORD_SIZE(sp)
  sw   t6, 28 * OT_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * OT_WORD_SIZE(sp)

  // Save MEPC to the stack after updating it to the next instruction (since
  // this is a synchronous IRQ).
  jal rom_compute_mepc_on_synchronous_irq
  sw t0, 0(sp)

  // Jump to the exception handler.
  mv a0, sp
  jal rom_exception_handler

  // Return from exception handler.
  j rom_exception_handler_exit
  .size rom_exception_handler_entry, .-rom_exception_handler_entry

// -----------------------------------------------------------------------------

  /**
   * Exception handler exit sub-routine restores registers from the stack.
   */
  .balign 4
  .global rom_exception_handler_exit
  .type rom_exception_handler_exit, @function
rom_exception_handler_exit:
  // Load the correct MEPC for the next instruction in the current task.
  lw t0, 0(sp)
  csrw mepc, t0

  // Load MSTATUS for the MPIE bit.
  lw  t0, 29 * OT_WORD_SIZE(sp)
  csrw mstatus, t0

  // Restore all registers from the stack.
  lw   ra,  1 * OT_WORD_SIZE(sp)
  lw   t0,  2 * OT_WORD_SIZE(sp)
  lw   t1,  3 * OT_WORD_SIZE(sp)
  lw   t2,  4 * OT_WORD_SIZE(sp)
  lw   s0,  5 * OT_WORD_SIZE(sp)
  lw   s1,  6 * OT_WORD_SIZE(sp)
  lw   a0,  7 * OT_WORD_SIZE(sp)
  lw   a1,  8 * OT_WORD_SIZE(sp)
  lw   a2,  9 * OT_WORD_SIZE(sp)
  lw   a3, 10 * OT_WORD_SIZE(sp)
  lw   a4, 11 * OT_WORD_SIZE(sp)
  lw   a5, 12 * OT_WORD_SIZE(sp)
  lw   a6, 13 * OT_WORD_SIZE(sp)
  lw   a7, 14 * OT_WORD_SIZE(sp)
  lw   s2, 15 * OT_WORD_SIZE(sp)
  lw   s3, 16 * OT_WORD_SIZE(sp)
  lw   s4, 17 * OT_WORD_SIZE(sp)
  lw   s5, 18 * OT_WORD_SIZE(sp)
  lw   s6, 19 * OT_WORD_SIZE(sp)
  lw   s7, 20 * OT_WORD_SIZE(sp)
  lw   s8, 21 * OT_WORD_SIZE(sp)
  lw   s9, 22 * OT_WORD_SIZE(sp)
  lw  s10, 23 * OT_WORD_SIZE(sp)
  lw  s11, 24 * OT_WORD_SIZE(sp)
  lw   t3, 25 * OT_WORD_SIZE(sp)
  lw   t4, 26 * OT_WORD_SIZE(sp)
  lw   t5, 27 * OT_WORD_SIZE(sp)
  lw   t6, 28 * OT_WORD_SIZE(sp)
  addi sp, sp, OT_CONTEXT_SIZE

  // This exits the ISR completely, and does not return control flow to the ISR
  // that called this sub-routine.
  mret
  .size rom_exception_handler_exit, .-rom_exception_handler_exit
