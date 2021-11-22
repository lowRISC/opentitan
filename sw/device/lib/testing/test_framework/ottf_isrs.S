// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_macros.h"

.extern pxCurrentTCB
.extern ottf_exception_handler
.extern ottf_software_isr
.extern ottf_timer_isr
.extern ottf_external_isr

// -----------------------------------------------------------------------------

/**
 * Compute the MEPC to that will be saved to the stack by the associated ISR
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
.type compute_mepc_on_synchronous_irq, @function
compute_mepc_on_synchronous_irq:
  csrr t0, mepc
  li t1, 0x3
  and t2, t0, t1
  beq t2, t1, L_32bit_trap_instr
  addi t0, t0, OTTF_HALF_WORD_SIZE
  ret
L_32bit_trap_instr:
  addi t0, t0, OTTF_WORD_SIZE
  ret

  // Set size so this function can be disassembled.
  .size compute_mepc_on_synchronous_irq, .-compute_mepc_on_synchronous_irq

// -----------------------------------------------------------------------------

/**
 * Exception handler.
 */
.balign 4
.global handler_exception
.type handler_exception, @function
handler_exception:
  // Save all registers to the stack.
  addi sp, sp, -OTTF_CONTEXT_SIZE
  sw   ra,  1 * OTTF_WORD_SIZE(sp)
  sw   t0,  2 * OTTF_WORD_SIZE(sp)
  sw   t1,  3 * OTTF_WORD_SIZE(sp)
  sw   t2,  4 * OTTF_WORD_SIZE(sp)
  sw   s0,  5 * OTTF_WORD_SIZE(sp)
  sw   s1,  6 * OTTF_WORD_SIZE(sp)
  sw   a0,  7 * OTTF_WORD_SIZE(sp)
  sw   a1,  8 * OTTF_WORD_SIZE(sp)
  sw   a2,  9 * OTTF_WORD_SIZE(sp)
  sw   a3, 10 * OTTF_WORD_SIZE(sp)
  sw   a4, 11 * OTTF_WORD_SIZE(sp)
  sw   a5, 12 * OTTF_WORD_SIZE(sp)
  sw   a6, 13 * OTTF_WORD_SIZE(sp)
  sw   a7, 14 * OTTF_WORD_SIZE(sp)
  sw   s2, 15 * OTTF_WORD_SIZE(sp)
  sw   s3, 16 * OTTF_WORD_SIZE(sp)
  sw   s4, 17 * OTTF_WORD_SIZE(sp)
  sw   s5, 18 * OTTF_WORD_SIZE(sp)
  sw   s6, 19 * OTTF_WORD_SIZE(sp)
  sw   s7, 20 * OTTF_WORD_SIZE(sp)
  sw   s8, 21 * OTTF_WORD_SIZE(sp)
  sw   s9, 22 * OTTF_WORD_SIZE(sp)
  sw  s10, 23 * OTTF_WORD_SIZE(sp)
  sw  s11, 24 * OTTF_WORD_SIZE(sp)
  sw   t3, 25 * OTTF_WORD_SIZE(sp)
  sw   t4, 26 * OTTF_WORD_SIZE(sp)
  sw   t5, 27 * OTTF_WORD_SIZE(sp)
  sw   t6, 28 * OTTF_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * OTTF_WORD_SIZE(sp)

  // Save MEPC to the stack after updating it to the next instruction (since
  // this is a synchronous IRQ).
  jal compute_mepc_on_synchronous_irq
  sw t0, 0(sp)

  // Store stack pointer to current TCB.
  lw t0, pxCurrentTCB
  sw sp, 0(t0)

  // Jump to the exception handler.
  jal ottf_exception_handler

  // Return from ISR.
  j ottf_isr_exit

  // Set size so this function can be disassembled.
  .size handler_exception, .-handler_exception

// -----------------------------------------------------------------------------

/**
 * Software IRQ handler.
 */
.balign 4
.global handler_irq_software
.type handler_irq_software, @function
handler_irq_software:
  // Save all registers to the stack.
  addi sp, sp, -OTTF_CONTEXT_SIZE
  sw   ra,  1 * OTTF_WORD_SIZE(sp)
  sw   t0,  2 * OTTF_WORD_SIZE(sp)
  sw   t1,  3 * OTTF_WORD_SIZE(sp)
  sw   t2,  4 * OTTF_WORD_SIZE(sp)
  sw   s0,  5 * OTTF_WORD_SIZE(sp)
  sw   s1,  6 * OTTF_WORD_SIZE(sp)
  sw   a0,  7 * OTTF_WORD_SIZE(sp)
  sw   a1,  8 * OTTF_WORD_SIZE(sp)
  sw   a2,  9 * OTTF_WORD_SIZE(sp)
  sw   a3, 10 * OTTF_WORD_SIZE(sp)
  sw   a4, 11 * OTTF_WORD_SIZE(sp)
  sw   a5, 12 * OTTF_WORD_SIZE(sp)
  sw   a6, 13 * OTTF_WORD_SIZE(sp)
  sw   a7, 14 * OTTF_WORD_SIZE(sp)
  sw   s2, 15 * OTTF_WORD_SIZE(sp)
  sw   s3, 16 * OTTF_WORD_SIZE(sp)
  sw   s4, 17 * OTTF_WORD_SIZE(sp)
  sw   s5, 18 * OTTF_WORD_SIZE(sp)
  sw   s6, 19 * OTTF_WORD_SIZE(sp)
  sw   s7, 20 * OTTF_WORD_SIZE(sp)
  sw   s8, 21 * OTTF_WORD_SIZE(sp)
  sw   s9, 22 * OTTF_WORD_SIZE(sp)
  sw  s10, 23 * OTTF_WORD_SIZE(sp)
  sw  s11, 24 * OTTF_WORD_SIZE(sp)
  sw   t3, 25 * OTTF_WORD_SIZE(sp)
  sw   t4, 26 * OTTF_WORD_SIZE(sp)
  sw   t5, 27 * OTTF_WORD_SIZE(sp)
  sw   t6, 28 * OTTF_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * OTTF_WORD_SIZE(sp)

  // Save MEPC to the stack after updating it to the next instruction (since
  // this is a synchronous IRQ).
  jal compute_mepc_on_synchronous_irq
  sw t0, 0(sp)

  // Store stack pointer to current TCB.
  lw t0, pxCurrentTCB
  sw sp, 0(t0)

  // Jump to the software ISR.
  jal ottf_software_isr

  // Return from ISR.
  j ottf_isr_exit

  // Set size so this function can be disassembled.
  .size handler_irq_software, .-handler_irq_software

// -----------------------------------------------------------------------------

/**
 * Timer IRQ handler.
 */
.balign 4
.global handler_irq_timer
.type handler_irq_timer, @function
handler_irq_timer:
  // Save all registers to the stack.
  addi sp, sp, -OTTF_CONTEXT_SIZE
  sw   ra,  1 * OTTF_WORD_SIZE(sp)
  sw   t0,  2 * OTTF_WORD_SIZE(sp)
  sw   t1,  3 * OTTF_WORD_SIZE(sp)
  sw   t2,  4 * OTTF_WORD_SIZE(sp)
  sw   s0,  5 * OTTF_WORD_SIZE(sp)
  sw   s1,  6 * OTTF_WORD_SIZE(sp)
  sw   a0,  7 * OTTF_WORD_SIZE(sp)
  sw   a1,  8 * OTTF_WORD_SIZE(sp)
  sw   a2,  9 * OTTF_WORD_SIZE(sp)
  sw   a3, 10 * OTTF_WORD_SIZE(sp)
  sw   a4, 11 * OTTF_WORD_SIZE(sp)
  sw   a5, 12 * OTTF_WORD_SIZE(sp)
  sw   a6, 13 * OTTF_WORD_SIZE(sp)
  sw   a7, 14 * OTTF_WORD_SIZE(sp)
  sw   s2, 15 * OTTF_WORD_SIZE(sp)
  sw   s3, 16 * OTTF_WORD_SIZE(sp)
  sw   s4, 17 * OTTF_WORD_SIZE(sp)
  sw   s5, 18 * OTTF_WORD_SIZE(sp)
  sw   s6, 19 * OTTF_WORD_SIZE(sp)
  sw   s7, 20 * OTTF_WORD_SIZE(sp)
  sw   s8, 21 * OTTF_WORD_SIZE(sp)
  sw   s9, 22 * OTTF_WORD_SIZE(sp)
  sw  s10, 23 * OTTF_WORD_SIZE(sp)
  sw  s11, 24 * OTTF_WORD_SIZE(sp)
  sw   t3, 25 * OTTF_WORD_SIZE(sp)
  sw   t4, 26 * OTTF_WORD_SIZE(sp)
  sw   t5, 27 * OTTF_WORD_SIZE(sp)
  sw   t6, 28 * OTTF_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * OTTF_WORD_SIZE(sp)

  // Save MEPC to the stack.
  // NOTE: this IRQ is asynchronous, therefore, we do not need to modify MEPC.
  csrr t0, mepc
  sw t0, 0(sp)

  // Store stack pointer to current TCB.
  lw t0, pxCurrentTCB
  sw sp, 0(t0)

  // Jump to timer ISR.
  jal ottf_timer_isr

  // Return from ISR.
  j ottf_isr_exit

  // Set size so this function can be disassembled.
  .size handler_irq_timer, .-handler_irq_timer

// -----------------------------------------------------------------------------

/**
 * External IRQ handler.
 */
.balign 4
.global handler_irq_external
.type handler_irq_external, @function
handler_irq_external:
  // Save all registers to the stack.
  addi sp, sp, -OTTF_CONTEXT_SIZE
  sw   ra,  1 * OTTF_WORD_SIZE(sp)
  sw   t0,  2 * OTTF_WORD_SIZE(sp)
  sw   t1,  3 * OTTF_WORD_SIZE(sp)
  sw   t2,  4 * OTTF_WORD_SIZE(sp)
  sw   s0,  5 * OTTF_WORD_SIZE(sp)
  sw   s1,  6 * OTTF_WORD_SIZE(sp)
  sw   a0,  7 * OTTF_WORD_SIZE(sp)
  sw   a1,  8 * OTTF_WORD_SIZE(sp)
  sw   a2,  9 * OTTF_WORD_SIZE(sp)
  sw   a3, 10 * OTTF_WORD_SIZE(sp)
  sw   a4, 11 * OTTF_WORD_SIZE(sp)
  sw   a5, 12 * OTTF_WORD_SIZE(sp)
  sw   a6, 13 * OTTF_WORD_SIZE(sp)
  sw   a7, 14 * OTTF_WORD_SIZE(sp)
  sw   s2, 15 * OTTF_WORD_SIZE(sp)
  sw   s3, 16 * OTTF_WORD_SIZE(sp)
  sw   s4, 17 * OTTF_WORD_SIZE(sp)
  sw   s5, 18 * OTTF_WORD_SIZE(sp)
  sw   s6, 19 * OTTF_WORD_SIZE(sp)
  sw   s7, 20 * OTTF_WORD_SIZE(sp)
  sw   s8, 21 * OTTF_WORD_SIZE(sp)
  sw   s9, 22 * OTTF_WORD_SIZE(sp)
  sw  s10, 23 * OTTF_WORD_SIZE(sp)
  sw  s11, 24 * OTTF_WORD_SIZE(sp)
  sw   t3, 25 * OTTF_WORD_SIZE(sp)
  sw   t4, 26 * OTTF_WORD_SIZE(sp)
  sw   t5, 27 * OTTF_WORD_SIZE(sp)
  sw   t6, 28 * OTTF_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * OTTF_WORD_SIZE(sp)

  // Save MEPC to the stack.
  // NOTE: this IRQ is asynchronous, therefore, we do not need to modify MEPC.
  csrr t0, mepc
  sw t0, 0(sp)

  // Store stack pointer to current TCB.
  lw t0, pxCurrentTCB
  sw sp, 0(t0)

  // Jump to external ISR.
  jal ottf_external_isr

  // Return from ISR.
  j ottf_isr_exit

  // Set size so this function can be disassembled.
  .size handler_irq_external, .-handler_irq_external

// -----------------------------------------------------------------------------

/**
 * ISR exit sub-routine restores registers from the stack.
 */
.balign 4
.global ottf_isr_exit
.type ottf_isr_exit, @function
ottf_isr_exit:
  // Load the stack pointer for the current TCB.
	lw  t1, pxCurrentTCB
	lw  sp, 0(t1)

  // Load the correct MEPC for the next instruction in the current task.
	lw t0, 0(sp)
	csrw mepc, t0

  // Load MSTATUS for the MPIE bit.
	lw  t0, 29 * OTTF_WORD_SIZE(sp)
	csrw mstatus, t0

  // Restore all registers from the stack.
  lw   ra,  1 * OTTF_WORD_SIZE(sp)
  lw   t0,  2 * OTTF_WORD_SIZE(sp)
  lw   t1,  3 * OTTF_WORD_SIZE(sp)
  lw   t2,  4 * OTTF_WORD_SIZE(sp)
  lw   s0,  5 * OTTF_WORD_SIZE(sp)
  lw   s1,  6 * OTTF_WORD_SIZE(sp)
  lw   a0,  7 * OTTF_WORD_SIZE(sp)
  lw   a1,  8 * OTTF_WORD_SIZE(sp)
  lw   a2,  9 * OTTF_WORD_SIZE(sp)
  lw   a3, 10 * OTTF_WORD_SIZE(sp)
  lw   a4, 11 * OTTF_WORD_SIZE(sp)
  lw   a5, 12 * OTTF_WORD_SIZE(sp)
  lw   a6, 13 * OTTF_WORD_SIZE(sp)
  lw   a7, 14 * OTTF_WORD_SIZE(sp)
  lw   s2, 15 * OTTF_WORD_SIZE(sp)
  lw   s3, 16 * OTTF_WORD_SIZE(sp)
  lw   s4, 17 * OTTF_WORD_SIZE(sp)
  lw   s5, 18 * OTTF_WORD_SIZE(sp)
  lw   s6, 19 * OTTF_WORD_SIZE(sp)
  lw   s7, 20 * OTTF_WORD_SIZE(sp)
  lw   s8, 21 * OTTF_WORD_SIZE(sp)
  lw   s9, 22 * OTTF_WORD_SIZE(sp)
  lw  s10, 23 * OTTF_WORD_SIZE(sp)
  lw  s11, 24 * OTTF_WORD_SIZE(sp)
  lw   t3, 25 * OTTF_WORD_SIZE(sp)
  lw   t4, 26 * OTTF_WORD_SIZE(sp)
  lw   t5, 27 * OTTF_WORD_SIZE(sp)
  lw   t6, 28 * OTTF_WORD_SIZE(sp)
  addi sp, sp, OTTF_CONTEXT_SIZE

  // This exits the ISR completely, and does not return control flow to the ISR
  // that called this sub-routine.
  mret

  // Set size so this function can be disassembled.
  .size ottf_isr_exit, .-ottf_isr_exit
