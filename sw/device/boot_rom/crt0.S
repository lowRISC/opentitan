// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

  .section .text

/**
 * Default exception handler; loops forever.
 */
exception_handler:
  j exception_handler

/**
 * Default interrupt handler; loops forever.
 */
default_irq_handler:
  j default_irq_handler

/**
 * Entry point after reset.
 *
 * Sets up the stack, then jumps to |_start|.
 */
reset_handler:
  // Clobber all writeable registers.
  li  x1, 0x0
  li  x2, 0x0
  li  x3, 0x0
  li  x4, 0x0
  li  x5, 0x0
  li  x6, 0x0
  li  x7, 0x0
  li  x8, 0x0
  li  x9, 0x0
  li  x10, 0x0
  li  x11, 0x0
  li  x12, 0x0
  li  x13, 0x0
  li  x14, 0x0
  li  x15, 0x0
  li  x16, 0x0
  li  x17, 0x0
  li  x18, 0x0
  li  x19, 0x0
  li  x20, 0x0
  li  x21, 0x0
  li  x22, 0x0
  li  x23, 0x0
  li  x24, 0x0
  li  x25, 0x0
  li  x26, 0x0
  li  x27, 0x0
  li  x28, 0x0
  li  x29, 0x0
  li  x30, 0x0
  li  x31, 0x0

  // Set up the stack.
  la  sp, _stack_start

  // Explicit fall-through to |_start|.

/**
 * Callable entry point for the boot rom.
 *
 * Currently, this only zeroes the |.bss| section, and, as such, any code
 * that currently uses the |.data| segment will not work.
 */
_start:
  .globl _start

  // Zero out the BSS segment.
  la  t0, _bss_start
  la  t1, _bss_end
  bge t0, t1, zero_loop_end
zero_loop:
  sw    zero, 0(t0)
  addi  t0, t0, 0x4
  ble   t0, t1, zero_loop
zero_loop_end:

  // Jump into the C program entry point.
  call  _boot_start
1:
  wfi
  j 1b

/**
 * Exception and interrupt handlers.
 *
 * This must be a separate section, since we disable RVC for it.
 */
  .section .vectors, "ax"
  .option norvc;

  // Exception handler.
  .org 0x00
  j exception_handler

  // Software interrupt handler.
  .org 0x0c
  j default_irq_handler

  // Timer interrupt handler.
  .org 0x1c
  j default_irq_handler

  // External interrupt handler
  .org 0x2c
  j default_irq_handler

  // Fast interrupts, 0 through 14.
  .org 0x40
  .rept 14
  nop
  .endr
  j default_irq_handler

  // Non-maskable interrupt (NMI) handler.
  .org 0x7c
  j default_irq_handler

  // Reset vector, the initial entry point after reset.
  .org 0x80
  j reset_handler
