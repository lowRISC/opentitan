// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_macros.h"

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
  lw   t1,  3 * OTTF_WORD_SIZE(sp)
  lw   t2,  4 * OTTF_WORD_SIZE(sp)
  lw   s0,  5 * OTTF_WORD_SIZE(sp)
  lw   s1,  6 * OTTF_WORD_SIZE(sp)
  lw   a0,  7 * OTTF_WORD_SIZE(sp) // task parameters (pvParameters)
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

  // Initialize t0 to the value of MSTATUS with global interrupts enabled, which
  // is required because this returns with ret, not eret.
  lw t0, 29 * OTTF_WORD_SIZE(sp) // Load the MSTATUS state from the stack.
  ori t0, t0, 1<<3               // Set MIE field.
  csrw mstatus, t0               // Ibex interrupts enabled from here!

  // Restore t0 register from the stack (after using it to manipulate MSTATUS).
  lw t0, 2 * OTTF_WORD_SIZE(sp)

  // Update the stack pointer (shrinking the stack).
  addi sp, sp, OTTF_CONTEXT_SIZE

  ret
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
  addi a0, a0, -OTTF_CONTEXT_SIZE
  // Push MSTATUS onto the stack.
  sw t0, 29 * OTTF_WORD_SIZE(a0)

  // Push task parameters (pvParameters that is in x12/a2, on the stack.
  sw a2, 7 * OTTF_WORD_SIZE(a0)
  // Push 0 for the portTASK_RETURN_ADDRESS for now.
  sw zero, 1 * OTTF_WORD_SIZE(a0)
  // Push the pointer to the task's entry point (pxCode) onto the stack. This
  // will be loaded into either ra (in xPortStartFirstTask) or mepc (in
  // freertosIrqExit), so that when ret/mret is called control flow will be
  // transferred accordingly.
  sw a1, 0(a0)

  ret
  .size pxPortInitialiseStack, .-pxPortInitialiseStack
