/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Elliptic curve P-384 ECDSA
 *
 * Uses OTBN ECC P-384 lib to perform an ECDSA operations.
 */

.section .text.start
.globl start
start:
  /* Read mode, then tail-call either p384_ecdsa_sign or p384_ecdsa_verify */
  la    x2, mode
  lw    x2, 0(x2)

  li    x3, 1
  beq   x2, x3, p384_ecdsa_sign

  li    x3, 2
  beq   x2, x3, p384_ecdsa_verify

  /* Mode is neither 1 (= sign) nor 2 (= verify). Fail. */
  unimp

.text
p384_ecdsa_sign:
  jal      x1, p384_sign
  ecall

p384_ecdsa_verify:
  /*jal      x1, p384_verify*/
  ecall

.bss

/* randomness for blinding */
.globl rnd
.balign 64
rnd:
  .zero 64
