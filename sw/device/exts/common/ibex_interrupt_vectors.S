// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * This file contains Ibex-specific interrupt vectors.
 */

  // These functions are declared in `sw/device/lib/handler.h`.
  .extern handler_exception
  .extern handler_irq_software
  .extern handler_irq_timer
  .extern handler_irq_external

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated space in ROM by the linker.
  .section .vectors, "ax"
  .option push
  // Switch off compressed instructions so we know each instruction below is
  // exactly 4 bytes (one entry).
  .option norvc
  // Switch off linker relaxation so that the linker does not reduce the size of
  // any entries.
  .option norelax

/**
 * `crt_interrupt_vector` is the CRT-loaded interrupt vector for Ibex.
 *
 * It contains entries that point at the functions declared in
 * `sw/device/lib/handler.h`. If you are getting link errors for these symbols,
 * then it's likely you have forgotten to add `sw_lib_irq_handlers` as a
 * dependency for your executable.
 *
 * Interrupt vectors in Ibex have 32 entries for 32 possible interrupts. The
 * vector must be 256-byte aligned, as Ibex's vectoring mechanism requires that.
 *
 * This vector has exactly 32 entries so that code after the vector will not
 * overlap the interrupt vector, which causes debugging confusion.
 *
 * More information about Ibex's interrupts can be found here:
 *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
 */
  .balign 256
crt_interrupt_vector:
  .global crt_interrupt_vector

  // exception Handler and user software interrupt
  j handler_exception
  // supervisor software interrupt
  unimp
  // reserved
  unimp
  // machine software interrupt handler
  j handler_irq_software

  // user timer interrupt
  unimp
  // supervisor timer interrupt
  unimp
  // reserved
  unimp
  // machine timer interrupt handler
  j handler_irq_timer

  // user external interrupt
  unimp
  // supervisor external interrupt
  unimp
  // reserved
  unimp
  // machine external interrupt handler
  j handler_irq_external

  // reserved
  unimp
  unimp
  unimp
  unimp

  // vendor interrupts: on Ibex interrupt ids 30-16 are the "fast" interrupts
  .rept 15
  unimp
  .endr

  // vendor interrupts: on Ibex interrupt id 31 is for non-maskable interrupts
  unimp

  // Set size so vector can be disassembled
  .size crt_interrupt_vector, .-crt_interrupt_vector

  .option pop
