// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * CRT library
 *
 * Utility functions written in assembly that can be used before the C
 * runtime has been initialized. These functions should not be used once
 * the C runtime has been initialized.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated space in ROM by the linker.
  .section .crt, "ax", @progbits

/**
 * Write zeros into the section bounded by the start and end pointers.
 * The section must be word (4 byte) aligned. It is valid for the section
 * to have a length of 0 (i.e. the start and end pointers may be equal).
 *
 * This function follows the standard ILP32 calling convention for arguments
 * but does not require a valid stack pointer, thread pointer or global
 * pointer.
 *
 * Clobbers a0 and t0.
 *
 * @param a0 pointer to start of section to clear (inclusive).
 * @param a1 pointer to end of section to clear (exclusive).
 */
crt_section_clear:
  .globl crt_section_clear
  .type crt_section_clear, @function

  // Check that start is before end.
  bgeu a0, a1, L_clear_nothing

  // Check that start and end are word aligned.
  or   t0, a0, a1
  andi t0, t0, 0x3
  bnez t0, L_clear_error

L_clear_loop:
  // Write zero into section memory word-by-word.
  // TODO: unroll
  sw   zero, 0(a0)
  addi a0, a0, 4
  bltu a0, a1, L_clear_loop
  ret

L_clear_nothing:
  // If section length is 0 just return. Otherwise end is before start
  // which is invalid so trigger an error.
  bne a0, a1, L_clear_error
  ret

L_clear_error:
  unimp

  // Set function size to allow disassembly.
  .size crt_section_clear, .-crt_section_clear

/**
 * Copy data from the given source into the section bounded by the start and
 * end pointers. Both the section and the source must be word (4 byte) aligned.
 * It is valid for the section to have a length of 0 (i.e. the start and end
 * pointers may be equal). The source is assumed to have the same length as the
 * target section.
 *
 * The destination section and the source must not overlap.
 *
 * This function follows the standard ILP32 calling convention for arguments
 * but does not require a valid stack pointer, thread pointer or global
 * pointer.
 *
 * Clobbers a0, a2, t0 and t1.
 *
 * @param a0 pointer to start of destination section (inclusive).
 * @param a1 pointer to end of destination section (exclusive).
 * @param a2 pointer to source data (inclusive).
 */
crt_section_copy:
  .global crt_section_copy
  .type crt_section_copy, @function

  // Check that start is before end.
  bgeu a0, a1, L_copy_nothing

  // Check that start, end and src are word aligned.
  or   t0, a0, a1
  or   t0, t0, a2
  andi t0, t0, 0x3
  bnez t0, L_copy_error

  // Check that source does not destructively overlap destination
  // (assuming a forwards copy).
  //
  // src  start          end
  //  |     |             |
  //  +-------------+     |
  //  |   source    |     |
  //  +-------------+     |
  //        +-------------+
  //        | destination |
  //        +-------------+
  //        |             |
  //      start          end
  //
  // TODO: disallow all overlap since it indicates API misuse?
  sub  t0, a0, a2           // (start - src) mod 2**32
  sub  t1, a1, a0           // end - start
  bltu t0, t1, L_copy_error

L_copy_loop:
  // Copy data from src into section word-by-word.
  // TODO: unroll
  lw   t0, 0(a2)
  addi a2, a2, 4
  sw   t0, 0(a0)
  addi a0, a0, 4
  bltu a0, a1, L_copy_loop
  ret

L_copy_nothing:
  // If section length is 0 just return. Otherwise end is before start
  // which is invalid so trigger an error.
  bne a0, a1, L_copy_error
  ret

L_copy_error:
  unimp

  // Set function size to allow disassembly.
  .size crt_section_copy, .-crt_section_copy
