// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Ibex does not implement additional registers beyond the RV32I spec.
#define PORT_WORD_SIZE 4
#define PORT_HALF_WORD_SIZE (PORT_WORD_SIZE / 2)
#define PORT_CONTEXT_SIZE (30 * PORT_WORD_SIZE)

.extern pxCurrentTCB
.extern xISRStackTop
.extern ottf_exception_handler
.extern ottf_software_isr
.extern ottf_timer_isr
.extern ottf_external_isr

// -----------------------------------------------------------------------------

/**
 * Save MEPC to the stack.
 *
 * NOTE: this IRQ is synchronous, therefore, we must update the ISR return
 * address to point to the instruction after the one that triggered this IRQ.
 * Since we support the RISC-V compressed instructions extension, we need to
 * check if the two least significant bits of the instruction are
 * b11 (0x3), which means that the trapped instruction is not compressed,
 * i.e., the trapped instruction is 32bits = 4bytes. Otherwise, the trapped
 * instruction is 16bits = 2bytes.
 */

.balign 4
.type process_mepc_on_synchronous_irq, @function
process_mepc_on_synchronous_irq:
  csrr t0, mepc
  li t1, 0x3
  and t2, t0, t1
  beq t2, t1, L_32bit_trap_instr
  addi t0, t0, PORT_HALF_WORD_SIZE
  ret
L_32bit_trap_instr:
  addi t0, t0, PORT_WORD_SIZE
  ret

  // Set size so this function can be disassembled.
  .size process_mepc_on_synchronous_irq, .-process_mepc_on_synchronous_irq

// -----------------------------------------------------------------------------

/**
 * Exception handler.
 */
.balign 4
.global handler_exception
.type handler_exception, @function
handler_exception:
  // Save all registers to the stack.
  addi sp, sp, -PORT_CONTEXT_SIZE
  sw   ra,  1 * PORT_WORD_SIZE(sp)
  sw   t0,  2 * PORT_WORD_SIZE(sp)
  sw   t1,  3 * PORT_WORD_SIZE(sp)
  sw   t2,  4 * PORT_WORD_SIZE(sp)
  sw   s0,  5 * PORT_WORD_SIZE(sp)
  sw   s1,  6 * PORT_WORD_SIZE(sp)
  sw   a0,  7 * PORT_WORD_SIZE(sp)
  sw   a1,  8 * PORT_WORD_SIZE(sp)
  sw   a2,  9 * PORT_WORD_SIZE(sp)
  sw   a3, 10 * PORT_WORD_SIZE(sp)
  sw   a4, 11 * PORT_WORD_SIZE(sp)
  sw   a5, 12 * PORT_WORD_SIZE(sp)
  sw   a6, 13 * PORT_WORD_SIZE(sp)
  sw   a7, 14 * PORT_WORD_SIZE(sp)
  sw   s2, 15 * PORT_WORD_SIZE(sp)
  sw   s3, 16 * PORT_WORD_SIZE(sp)
  sw   s4, 17 * PORT_WORD_SIZE(sp)
  sw   s5, 18 * PORT_WORD_SIZE(sp)
  sw   s6, 19 * PORT_WORD_SIZE(sp)
  sw   s7, 20 * PORT_WORD_SIZE(sp)
  sw   s8, 21 * PORT_WORD_SIZE(sp)
  sw   s9, 22 * PORT_WORD_SIZE(sp)
  sw  s10, 23 * PORT_WORD_SIZE(sp)
  sw  s11, 24 * PORT_WORD_SIZE(sp)
  sw   t3, 25 * PORT_WORD_SIZE(sp)
  sw   t4, 26 * PORT_WORD_SIZE(sp)
  sw   t5, 27 * PORT_WORD_SIZE(sp)
  sw   t6, 28 * PORT_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * PORT_WORD_SIZE(sp)

  // Save MEPC to the stack after updating it to the next instruction (since
  // this is a synchronous IRQ).
  jal process_mepc_on_synchronous_irq
  sw t0, 0(sp)

  // Store stack pointer to current TCB.
  lw t0, pxCurrentTCB
  sw sp, 0(t0)

  // Jump to the exception handler.
  jal ottf_exception_handler

  // Return from ISR.
  j freertosIrqExit

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
  addi sp, sp, -PORT_CONTEXT_SIZE
  sw   ra,  1 * PORT_WORD_SIZE(sp)
  sw   t0,  2 * PORT_WORD_SIZE(sp)
  sw   t1,  3 * PORT_WORD_SIZE(sp)
  sw   t2,  4 * PORT_WORD_SIZE(sp)
  sw   s0,  5 * PORT_WORD_SIZE(sp)
  sw   s1,  6 * PORT_WORD_SIZE(sp)
  sw   a0,  7 * PORT_WORD_SIZE(sp)
  sw   a1,  8 * PORT_WORD_SIZE(sp)
  sw   a2,  9 * PORT_WORD_SIZE(sp)
  sw   a3, 10 * PORT_WORD_SIZE(sp)
  sw   a4, 11 * PORT_WORD_SIZE(sp)
  sw   a5, 12 * PORT_WORD_SIZE(sp)
  sw   a6, 13 * PORT_WORD_SIZE(sp)
  sw   a7, 14 * PORT_WORD_SIZE(sp)
  sw   s2, 15 * PORT_WORD_SIZE(sp)
  sw   s3, 16 * PORT_WORD_SIZE(sp)
  sw   s4, 17 * PORT_WORD_SIZE(sp)
  sw   s5, 18 * PORT_WORD_SIZE(sp)
  sw   s6, 19 * PORT_WORD_SIZE(sp)
  sw   s7, 20 * PORT_WORD_SIZE(sp)
  sw   s8, 21 * PORT_WORD_SIZE(sp)
  sw   s9, 22 * PORT_WORD_SIZE(sp)
  sw  s10, 23 * PORT_WORD_SIZE(sp)
  sw  s11, 24 * PORT_WORD_SIZE(sp)
  sw   t3, 25 * PORT_WORD_SIZE(sp)
  sw   t4, 26 * PORT_WORD_SIZE(sp)
  sw   t5, 27 * PORT_WORD_SIZE(sp)
  sw   t6, 28 * PORT_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * PORT_WORD_SIZE(sp)

  // Save MEPC to the stack after updating it to the next instruction (since
  // this is a synchronous IRQ).
  jal process_mepc_on_synchronous_irq
  sw t0, 0(sp)

  // Store stack pointer to current TCB.
  lw t0, pxCurrentTCB
  sw sp, 0(t0)

  // Jump to the software ISR.
  jal ottf_software_isr

  // Return from ISR.
  j freertosIrqExit

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
  addi sp, sp, -PORT_CONTEXT_SIZE
  sw   ra,  1 * PORT_WORD_SIZE(sp)
  sw   t0,  2 * PORT_WORD_SIZE(sp)
  sw   t1,  3 * PORT_WORD_SIZE(sp)
  sw   t2,  4 * PORT_WORD_SIZE(sp)
  sw   s0,  5 * PORT_WORD_SIZE(sp)
  sw   s1,  6 * PORT_WORD_SIZE(sp)
  sw   a0,  7 * PORT_WORD_SIZE(sp)
  sw   a1,  8 * PORT_WORD_SIZE(sp)
  sw   a2,  9 * PORT_WORD_SIZE(sp)
  sw   a3, 10 * PORT_WORD_SIZE(sp)
  sw   a4, 11 * PORT_WORD_SIZE(sp)
  sw   a5, 12 * PORT_WORD_SIZE(sp)
  sw   a6, 13 * PORT_WORD_SIZE(sp)
  sw   a7, 14 * PORT_WORD_SIZE(sp)
  sw   s2, 15 * PORT_WORD_SIZE(sp)
  sw   s3, 16 * PORT_WORD_SIZE(sp)
  sw   s4, 17 * PORT_WORD_SIZE(sp)
  sw   s5, 18 * PORT_WORD_SIZE(sp)
  sw   s6, 19 * PORT_WORD_SIZE(sp)
  sw   s7, 20 * PORT_WORD_SIZE(sp)
  sw   s8, 21 * PORT_WORD_SIZE(sp)
  sw   s9, 22 * PORT_WORD_SIZE(sp)
  sw  s10, 23 * PORT_WORD_SIZE(sp)
  sw  s11, 24 * PORT_WORD_SIZE(sp)
  sw   t3, 25 * PORT_WORD_SIZE(sp)
  sw   t4, 26 * PORT_WORD_SIZE(sp)
  sw   t5, 27 * PORT_WORD_SIZE(sp)
  sw   t6, 28 * PORT_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * PORT_WORD_SIZE(sp)

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
  j freertosIrqExit

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
  addi sp, sp, -PORT_CONTEXT_SIZE
  sw   ra,  1 * PORT_WORD_SIZE(sp)
  sw   t0,  2 * PORT_WORD_SIZE(sp)
  sw   t1,  3 * PORT_WORD_SIZE(sp)
  sw   t2,  4 * PORT_WORD_SIZE(sp)
  sw   s0,  5 * PORT_WORD_SIZE(sp)
  sw   s1,  6 * PORT_WORD_SIZE(sp)
  sw   a0,  7 * PORT_WORD_SIZE(sp)
  sw   a1,  8 * PORT_WORD_SIZE(sp)
  sw   a2,  9 * PORT_WORD_SIZE(sp)
  sw   a3, 10 * PORT_WORD_SIZE(sp)
  sw   a4, 11 * PORT_WORD_SIZE(sp)
  sw   a5, 12 * PORT_WORD_SIZE(sp)
  sw   a6, 13 * PORT_WORD_SIZE(sp)
  sw   a7, 14 * PORT_WORD_SIZE(sp)
  sw   s2, 15 * PORT_WORD_SIZE(sp)
  sw   s3, 16 * PORT_WORD_SIZE(sp)
  sw   s4, 17 * PORT_WORD_SIZE(sp)
  sw   s5, 18 * PORT_WORD_SIZE(sp)
  sw   s6, 19 * PORT_WORD_SIZE(sp)
  sw   s7, 20 * PORT_WORD_SIZE(sp)
  sw   s8, 21 * PORT_WORD_SIZE(sp)
  sw   s9, 22 * PORT_WORD_SIZE(sp)
  sw  s10, 23 * PORT_WORD_SIZE(sp)
  sw  s11, 24 * PORT_WORD_SIZE(sp)
  sw   t3, 25 * PORT_WORD_SIZE(sp)
  sw   t4, 26 * PORT_WORD_SIZE(sp)
  sw   t5, 27 * PORT_WORD_SIZE(sp)
  sw   t6, 28 * PORT_WORD_SIZE(sp)

  // Save MSTATUS for the MPIE bit.
  csrr t0, mstatus
  sw t0, 29 * PORT_WORD_SIZE(sp)

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
  j freertosIrqExit

  // Set size so this function can be disassembled.
  .size handler_irq_external, .-handler_irq_external

// -----------------------------------------------------------------------------

/**
 * ISR exit sub-routine restores registers from the stack.
 */
.balign 4
.global freertosIrqExit
.type freertosIrqExit, @function
freertosIrqExit:
  // Load the stack pointer for the current TCB.
	lw  t1, pxCurrentTCB
	lw  sp, 0(t1)

  // Load the correct MEPC for the next instruction in the current task.
	lw t0, 0(sp)
	csrw mepc, t0

  // Load MSTATUS for the MPIE bit.
	lw  t0, 29 * PORT_WORD_SIZE(sp)
	csrw mstatus, t0

  // Restore all registers from the stack.
  lw   ra,  1 * PORT_WORD_SIZE(sp)
  lw   t0,  2 * PORT_WORD_SIZE(sp)
  lw   t1,  3 * PORT_WORD_SIZE(sp)
  lw   t2,  4 * PORT_WORD_SIZE(sp)
  lw   s0,  5 * PORT_WORD_SIZE(sp)
  lw   s1,  6 * PORT_WORD_SIZE(sp)
  lw   a0,  7 * PORT_WORD_SIZE(sp)
  lw   a1,  8 * PORT_WORD_SIZE(sp)
  lw   a2,  9 * PORT_WORD_SIZE(sp)
  lw   a3, 10 * PORT_WORD_SIZE(sp)
  lw   a4, 11 * PORT_WORD_SIZE(sp)
  lw   a5, 12 * PORT_WORD_SIZE(sp)
  lw   a6, 13 * PORT_WORD_SIZE(sp)
  lw   a7, 14 * PORT_WORD_SIZE(sp)
  lw   s2, 15 * PORT_WORD_SIZE(sp)
  lw   s3, 16 * PORT_WORD_SIZE(sp)
  lw   s4, 17 * PORT_WORD_SIZE(sp)
  lw   s5, 18 * PORT_WORD_SIZE(sp)
  lw   s6, 19 * PORT_WORD_SIZE(sp)
  lw   s7, 20 * PORT_WORD_SIZE(sp)
  lw   s8, 21 * PORT_WORD_SIZE(sp)
  lw   s9, 22 * PORT_WORD_SIZE(sp)
  lw  s10, 23 * PORT_WORD_SIZE(sp)
  lw  s11, 24 * PORT_WORD_SIZE(sp)
  lw   t3, 25 * PORT_WORD_SIZE(sp)
  lw   t4, 26 * PORT_WORD_SIZE(sp)
  lw   t5, 27 * PORT_WORD_SIZE(sp)
  lw   t6, 28 * PORT_WORD_SIZE(sp)
  addi sp, sp, PORT_CONTEXT_SIZE

  // This exits the ISR completely, and does not return control flow to the ISR
  // that called this sub-routine.
  mret

  // Set size so this function can be disassembled.
  .size freertosIrqExit, .-freertosIrqExit
// -----------------------------------------------------------------------------

/**
 * FreeRTOS, expects this function to exist and uses it to start the first task. 
 */
.balign 4
.global xPortStartFirstTask
.type xPortStartFirstTask, @function
xPortStartFirstTask:

  // Load the stack pointer for the current TCB (just going to clobber sp here
  // since we are setting it here anyway).
  lw  sp, pxCurrentTCB
  lw  sp, 0(sp)

  // NOTE: for starting the FreeRTOS scheduler, the exception return address is
  // used as the function return address. See pxPortInitialiseStack below.
  lw  ra, 0(sp)

  // Restore registers initialized on task start.
  lw   t1,  3 * PORT_WORD_SIZE(sp)
  lw   t2,  4 * PORT_WORD_SIZE(sp)
  lw   s0,  5 * PORT_WORD_SIZE(sp)
  lw   s1,  6 * PORT_WORD_SIZE(sp)
  lw   a0,  7 * PORT_WORD_SIZE(sp) // task parameters (pvParameters)
  lw   a1,  8 * PORT_WORD_SIZE(sp)
  lw   a2,  9 * PORT_WORD_SIZE(sp)
  lw   a3, 10 * PORT_WORD_SIZE(sp)
  lw   a4, 11 * PORT_WORD_SIZE(sp)
  lw   a5, 12 * PORT_WORD_SIZE(sp)
  lw   a6, 13 * PORT_WORD_SIZE(sp)
  lw   a7, 14 * PORT_WORD_SIZE(sp)
  lw   s2, 15 * PORT_WORD_SIZE(sp)
  lw   s3, 16 * PORT_WORD_SIZE(sp)
  lw   s4, 17 * PORT_WORD_SIZE(sp)
  lw   s5, 18 * PORT_WORD_SIZE(sp)
  lw   s6, 19 * PORT_WORD_SIZE(sp)
  lw   s7, 20 * PORT_WORD_SIZE(sp)
  lw   s8, 21 * PORT_WORD_SIZE(sp)
  lw   s9, 22 * PORT_WORD_SIZE(sp)
  lw  s10, 23 * PORT_WORD_SIZE(sp)
  lw  s11, 24 * PORT_WORD_SIZE(sp)
  lw   t3, 25 * PORT_WORD_SIZE(sp)
  lw   t4, 26 * PORT_WORD_SIZE(sp)
  lw   t5, 27 * PORT_WORD_SIZE(sp)
  lw   t6, 28 * PORT_WORD_SIZE(sp)

  // Initialize t0 to the value of MSTATUS with global interrupts enabled, which
  // is required because this returns with ret, not eret.
  lw t0, 29 * PORT_WORD_SIZE(sp) // Load the MSTATUS state from the stack.
  ori t0, t0, 1<<3               // Set MIE field.
  csrw mstatus, t0               // Ibex interrupts enabled from here!

  // Restore t0 register from the stack (after using it to manipulate MSTATUS).
  lw t0, 2 * PORT_WORD_SIZE(sp)

  // Update the stack pointer (shrinking the stack).
  addi sp, sp, PORT_CONTEXT_SIZE

  ret

  // Set size so this function can be disassembled.
  .size xPortStartFirstTask, .-xPortStartFirstTask

// -----------------------------------------------------------------------------

/** 
 * The prototype for this function depends on configurations defined in
 * FreeRTOSConfig.h, and is defined in:
 * sw/vendor/freertos_freertos_kernel/include/portable.h
 * 
 * The implementation of this assembly function assumes the prototype for this
 * function looks like:
 * 
 * StackType_t *pxPortInitialiseStack(StackType_t *pxTopOfStack,
 *                                    TaskFunction_t pxCode,
 *                                    void *pvParameters);
 * 
 * TODO: add some checks to verify this is the configured prototype.
 * TODO: configure to allow use of checking for stack overflows.
 * TODO: configure return address for first (main) task.
 * 
 * As per the standard RISC-V ABI pxTopcOfStack is passed in in a0, pxCode in
 * a1, and pvParameters in a2. The new top of stack is passed out in a0.
 * 
 * The RISC-V context is saved to FreeRTOS tasks in the following stack frame,
 * where the global and thread pointers are currently assumed to be constant,
 * and therefore are not saved:
 * 
 * ---Stack Bottom---
 * ---............---
 * Offset - Reg/Value
 *     29 - mstatus
 *     28 - t6 (x31)
 *     27 - t5 (x30)
 *     26 - t4 (x29)
 *     25 - t3 (x28)
 *     24 - s11 (x27)
 *     23 - s10 (x26)
 *     22 - s9 (x25)
 *     21 - s8 (x24)
 *     20 - s7 (x23)
 *     19 - s6 (x22)
 *     18 - s5 (x21)
 *     17 - s4 (x20)
 *     16 - s3 (x19)
 *     15 - s2 (x18)
 *     14 - a7 (x17)
 *     13 - a6 (x16)
 *     12 - a5 (x15)
 *     11 - a4 (x14)
 *     10 - a3 (x13)
 *      9 - a2 (x12)
 *      8 - a1 (x11)
 *      7 - (pvParameters)
 *      6 - s1 (x9)
 *      5 - s0 (x8)
 *      4 - t2 (x7)
 *      3 - t1 (x6)
 *      2 - t0 (x5)
 *      1 - (return address for main task, 0 for now)
 *      0 - (pxCode)
 * -----Stack Top----
 */
.balign 4
.global pxPortInitialiseStack
.type pxPortInitialiseStack, @function
pxPortInitialiseStack:

  // Setup the MSTATUS register.
  csrr t0, mstatus
  // Ensure interrupts are disabled when the stack is restored within an ISR.
  // Required when a task is created after the scheduler has been started,
  // otherwise interrupts would be disabled anyway.
  andi t0, t0, ~0x8
  // Generate the value 0x1880, to set the MPIE and MPP bits in MSTATUS.
  li t1, 0x188 << 4
  or t0, t0, t1

  // Setup the stack frame detailed above (a0 holds the task stack pointer).
  addi a0, a0, -PORT_CONTEXT_SIZE
  // Push MSTATUS onto the stack.
  sw t0, 29 * PORT_WORD_SIZE(a0)

  // Push task parameters (pvParameters that is in x12/a2, on the stack.
  sw a2, 7 * PORT_WORD_SIZE(a0)
  // Push 0 for the portTASK_RETURN_ADDRESS for now.
  sw zero, 1 * PORT_WORD_SIZE(a0)
  // Push the pointer to the task's entry point (pxCode) onto the stack. This
  // will be loaded into either ra (in xPortStartFirstTask) or mepc (in
  // freertosIrqExit), so that when ret/mret is called control flow will be
  // transferred accordingly.
  sw a1, 0(a0)

  ret

  // Set size so this function can be disassembled.
  .size pxPortInitialiseStack, .-pxPortInitialiseStack
