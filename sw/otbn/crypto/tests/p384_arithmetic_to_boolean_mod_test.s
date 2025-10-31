/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-384 arithmetic-to-boolean masking test
 *
 * Uses OTBN ECC P-384 lib to perform arithmetic-to-boolean conversion of
 * a given masked curve value with a random mask. Afterwards it unmasks the
 * result and compares it with the initial value from DMEM.
 */

.section .text.start

p384_arithmetic_to_boolean_mod_test:

  /* Load domain parameter.
     [w14,w13] = dmem[p384_p] */
  li        x2, 13
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Arithmetic to boolean conversion */
  jal       x1, p384_arithmetic_to_boolean_mod

  /* Unmask after conversion */

  /* w20 <= w20 ^ w18 = x' ^ r
     w21 <= w21 ^ w19 = x' ^ r */
  bn.xor    w20, w20, w18
  bn.xor    w21, w21, w19

  ecall
