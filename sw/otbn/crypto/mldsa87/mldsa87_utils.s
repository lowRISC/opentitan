/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl zeroize

.text

/**
 * Set n 256-bit DMEM words to 0.
 *
 * @param[in] x20: DMEM address of the first 256-bit word.
 * @param[in] x21: n, number of 256-bit to be set to 0.
 */
zeroize:
  addi x22, x0, 31
  loop x21, 1
    bn.sid x22, 0(x20++)
    /* End of loop */
  ret
