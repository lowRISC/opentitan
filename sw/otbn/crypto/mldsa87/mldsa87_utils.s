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

/**
 * Unmask n vectors of 8 Boolean-shared coefficients in-place.
 *
 * CAUTION: INSECURE! Only use for testing purposes.
 *
 * @param[in] x20: DMEM address of the first share.
 * @param[in] x21: DMEM address of the second share.
 * @param[in] x22: n, Number of 8-coefficients vectors to unmask.
 */
unmask_boolean:
  addi x23, x0, 0
  addi x24, x0, 1
  loop x22, 4
    bn.lid x23, 0(x20)
    bn.lid x24, 0(x21++)
    bn.xor w0, w0, w1
    bn.sid x23, 0(x20++)
    /* End of loop */
  ret

/**
 * Unmask n vectors of 8 arithmetically shared coefficients in-place.
 *
 * CAUTION: INSECURE! Only use for testing purposes.
 *
 * @param[in] x20: DMEM address of the first share.
 * @param[in] x21: DMEM address of the second share.
 * @param[in] x22: n, Number of 8-coefficients vectors to unmask.
 */
unmask_arithmetic:
  addi x23, x0, 0
  addi x24, x0, 1
  loop x22, 4
    bn.lid x23, 0(x20)
    bn.lid x24, 0(x21++)
    bn.addvm.8s w0, w0, w1
    bn.sid x23, 0(x20++)
    /* End of loop */
  ret
