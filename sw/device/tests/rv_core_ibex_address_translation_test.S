// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Converts every ASCII capital letter to a lowercase letter
 * until a NULL character is encountered.
 *
 * @param a0 pointer to the beginning of the null terminated string.
 */
  .globl make_lower_case
  .type make_lower_case, @function
  .balign 256
make_lower_case:
  // a0: beginning of string
  // t0, t1: lower and upper bound of ascii capital letters
  li t0, 0x41
  li t1, 0x5A

  addi a0, a0, -1
make_lower_case_loop:
  addi a0, a0, 1
  lb t2, 0(a0)

  // Break from the loop if the end of the given string is reached.
  beqz t2, make_lower_case_end

  // If not a capital letter, skip.
  bltu t2, t0, make_lower_case_loop
  bgtu t2, t1, make_lower_case_loop

  // Make character lower case.
  xori t2, t2, 0x20
  sb t2, 0(a0)
  j make_lower_case_loop

make_lower_case_end:
  ret

/**
 * The size of the `make_lower_case` function in bytes.
 */
  .global kMakeLowerCaseFnSize
kMakeLowerCaseFnSize:
  .4byte .-make_lower_case


/**
 * Replaces the content of the given string with a constant string (`name`)
 * until a NULL character is encountered in either the given string
 * or the constant string.
 *
 * @param a0 pointer to the beginning of the null terminated string.
 */
  .globl get_name
  .type get_name, @function
  .balign 256
get_name:
  // a0: beginning of string.
  // t0: beginning of replace string.
  lui t0, %hi(name)
  addi t0, t0, %lo(name)

  // t1: relative string pointer (cursor).
  mv t1, zero

get_name_loop:
  // Load current character from the string
  // and break if it is the last (NULL) character.
  add t2, t1, a0
  lb t4, 0(t2)
  beqz t4, get_name_end

  // Move the charater from the constant string into the given string.
  add t3, t1, t0
  lb t4, 0(t3)
  sb t4, 0(t2)
  // Break if that was the last character (NULL) of the constant string.
  beqz t4, get_name_end

  // Increment string pointer.
  addi t1, t1, 1
  j get_name_loop

get_name_end:
  ret

name:
  .string "My name is Titan, Open Titan"

/**
 * The size of the `get_name` function in bytes.
 */
  .global kGetNameFnSize
kGetNameFnSize:
  .4byte .-get_name
