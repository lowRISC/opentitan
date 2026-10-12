/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.include "mldsa87.inc"

/*
 * Standalone ML-DSA-87 OTBN app.
 *
 * Dispatches to the keygen, sign or verify routine depending on the mode
 * stored in `mldsa87_mode` (see `mldsa87.inc` for the mode identifiers).
 */

.section .text.start

run_mldsa87:
  la x2, mldsa87_mode
  lw x2, 0(x2)

  li x3, MLDSA87_MODE_KEYGEN_RND
  beq x2, x3, _run_mldsa87_keygen
  li x3, MLDSA87_MODE_KEYGEN_DET
  beq x2, x3, _run_mldsa87_keygen
  li x3, MLDSA87_MODE_SIGN_ABRIDGED
  beq x2, x3, _run_mldsa87_sign
  li x3, MLDSA87_MODE_SIGN_RND
  beq x2, x3, _run_mldsa87_sign
  li x3, MLDSA87_MODE_SIGN_DET
  beq x2, x3, _run_mldsa87_sign
  li x3, MLDSA87_MODE_VERIFY
  beq x2, x3, _run_mldsa87_verify

  /* Invalid mode. */
  unimp
  unimp
  unimp

_run_mldsa87_keygen:
  jal x1, mldsa87_keygen
  ecall

_run_mldsa87_sign:
  jal x1, mldsa87_sign
  ecall

_run_mldsa87_verify:
  jal x1, mldsa87_verify
  ecall
