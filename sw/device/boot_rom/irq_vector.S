// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Interrupt handler vector, set up so that all interrupts are 
 * caught and loop forever.
 *
 * See the Ibex manual, Chapter 11, for more information.
 */
  // NOTE: The "ax" flag below is necessary to ensure that this section 
  // is allocated executable space in ROM by the linker.
  .section .vectors, "ax"
  .option push

  // Disable RISC-V instruction compression: we need all instructions to 
  // be exactly word wide in the interrupt vector.
  .option norvc

  // Disable RISC-V linker relaxation, as it can compress instructions at
  // link-time, which we also really don't want.
  .option norelax

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
  // Since there are 15 of these in a continuous block,
  // we just repeat the same instruction.
  .org 0x40
  .rept 15
  j default_irq_handler
  .endr

  // Non-maskable interrupt (NMI) handler.
  .org 0x7c
  j default_irq_handler

  // Reset vector, the initial entry point after reset.
  .org 0x80
  j _reset_start

  .option pop

  // Put these handlers in the code section.
  .text
/**
 * Default exception handler; loops forever.
 */
exception_handler:
  wfi
  j exception_handler

/**
 * Default interrupt handler; loops forever.
 */
default_irq_handler:
  wfi
  j default_irq_handler
