/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 arithmetic-to-boolean masking test
 *
 * Uses OTBN ECC P-256 lib to perform arithmetic-to-boolean conversion of
 * a given masked curve value with a random mask. Afterwards it unmasks the
 * result and compares it with the initial value from DMEM.
 */

.section .text.start

p256_arithmetic_to_boolean_mod_test:

  /* Load domain parameter.
     w29 = dmem[p256_p] */
  li        x2, 29
  la        x4, p256_p
  bn.lid    x2, 0(x4)

  /* Set MOD to p */
  bn.wsrw   MOD, w29

  /* Arithmetic to boolean conversion */
  jal       x1, arithmetic_to_boolean_mod

  /* Unmask after conversion */

  /* w20 <= w20 ^ w19 = x' ^ r = x */
  bn.xor    w20, w20, w19

  ecall

.data

/* Public key z-coordinate. */
.globl z
.balign 32
z:
  .zero 32
