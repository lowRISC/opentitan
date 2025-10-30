/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone 384-bit boolean-to-arithmetic masking test
 *
 * Uses OTBN ECC P-384 lib to perform arithmetic-to-boolean conversion of
 * a given masked 384-bit value with a random mask. Afterwards it unmasks the
 * result and compares it with the initial value from DMEM.
 */

.section .text.start

p384_boolean_to_arithmetic_test:

  /* Arithmetic to boolean conversion */
  jal       x1, p384_boolean_to_arithmetic

  /* Unmask after conversion */

  /* [w21,w20] <= [w21,w20] + [w11,w10] = A + r */
  bn.add    w20, w20, w10
  bn.addc   w21, w21, w11

  ecall
