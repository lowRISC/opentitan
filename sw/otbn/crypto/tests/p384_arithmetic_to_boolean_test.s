/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone 385-bit arithmetic-to-boolean masking test
 *
 * Uses OTBN ECC P-384 lib to perform arithmetic-to-boolean conversion of
 * a given masked 385-bit value with a random mask. Afterwards it unmasks the
 * result and compares it with the initial value from DMEM.
 */

.section .text.start

p384_arithmetic_to_boolean_test:

  /* Arithmetic to boolean conversion */
  jal       x1, p384_arithmetic_to_boolean

  /* Unmask after conversion */

  /* w20 <= w20 ^ w18 = x' ^ r
     w21 <= w21 ^ w19 = x' ^ r */
  bn.xor    w20, w20, w18
  bn.xor    w21, w21, w19

  ecall
