/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial arithmetic over Z_q[X] / (X^256 + 1). */

.globl poly_mul
.globl poly_add
.globl poly_sub
.globl poly_mul_add

.text

/**
 * Pointwise Montgomery multiplication of two polynomials a(X) and b(X) over
 * Z_q[X] / (X^256 + 1).
 *
 * Both a and b are assumed to be stored in 1024-byte (256 32-bit coefficient
 * slots) regions in DMEM. Depending on whether {x2, x3} == x4, this routine is
 * either in-place or not.
 *
 * The caller must ensure that the modulus q and the corresponding Montgomery
 * multiplication constant have been correctly prepared (see the `MOD` register
 * and usage of the `bn.{add,sub,mul}vm` instructions) prior to invoking this
 * routine.
 *
 * CAUTION: The coefficients of a(X) and b(X) are not mapped into the
 * Montgomery space nor are the output coefficients converted back. It is the
 * responsibility of the caller to appropriately adjust the input/output
 * polynomials. For example, if two coefficients x and y are given as is, then
 * the resulting Montgomery mulplication will result in x * y * R^-1 mod q,
 * where R = 2^32.
 *
 * @param[in] x2: DMEM address of the polynomial a(X).
 * @param[in] x3: DMEM address of the polynomial b(X).
 * @param[in] x4: DMEM address of the result a(X) * b(X) * R^-1 mod q.
 */
poly_mul:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x2, x3, x4, x5
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* WDR pointer for the coefficients of b(X). */
  addi x5, x0, 1

  /* Each iteration calculates the modular addition of 8 coefficients. */
  loopi 32, 5
    /* Load 8 coefficients of a(X) and b(X) into w0 and w1. */
    bn.lid x0, 0(x2++)
    bn.lid x5, 0(x3++)

    /* Execute the vectorized Montgomery multiplication. */
    bn.mulvm.8S w0, w0, w1
    bn.addvm.8S w0, w0, w31 /* cond sub */

    /* Store the result back to DMEM. */
    bn.sid x0, 0(x4++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Modular addition of two polynomials a(X) and b(X) over Z_q[X] / (X^256 + 1).
 *
 * Both a and b are assumed to be stored in 1024-byte (256 32-bit coefficient
 * slots) regions in DMEM. Depending on whether {x2, x3} == x4, this routine is
 * either in-place or not.
 *
 * The caller must ensure that the modulus q has been correctly prepared (see
 * the `MOD` register and usage of the `bn.{add,sub,mul}vm` instructions) prior
 * to invoking this routine.
 *
 * @param[in] x2: DMEM address of the polynomial a(X).
 * @param[in] x3: DMEM address of the polynomial b(X).
 * @param[in] x4: DMEM address of the result a(X) + b(X) mod q.
 */
poly_add:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x2, x3, x4, x5
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* WDR pointer for the coefficients of b(X). */
  addi x5, x0, 1

  /* Each iteration calculates the modular addition of 8 coefficients. */
  loopi 32, 4
    /* Load 8 coefficients of a(X) and b(X) into w0 and w1. */
    bn.lid x0, 0(x2++)
    bn.lid x5, 0(x3++)

    /* Execute the vectorized modular addition. */
    bn.addvm.8S w0, w0, w1

    /* Store the result back to DMEM. */
    bn.sid x0, 0(x4++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Modular subtraction of two polynomials a(X) and b(X) over
 * Z_q[X] / (X^256 + 1).
 *
 * Both a and b are assumed to be stored in 1024-byte (256 32-bit coefficient
 * slots) regions in DMEM. Depending on whether {x2, x3} == x4, this routine is
 * either in-place or not.
 *
 * The caller must ensure that the modulus q has been correctly prepared (see
 * the `MOD` register and usage of the `bn.{add,sub,mul}vm` instructions) prior
 * to invoking this routine.
 *
 * @param[in] x2: DMEM address of the polynomial a(X).
 * @param[in] x3: DMEM address of the polynomial b(X).
 * @param[in] x4: DMEM address of the result a(X) - b(X) mod q.
 */
poly_sub:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x2, x3, x4, x5
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* WDR pointer for the coefficients of b(X). */
  addi x5, x0, 1

  /* Each iteration calculates the modular addition of 8 coefficients. */
  loopi 32, 4
    /* Load 8 coefficients of a(X) and b(X) into w0 and w1. */
    bn.lid x0, 0(x2++)
    bn.lid x5, 0(x3++)

    /* Execute the vectorized modular subtraction. */
    bn.subvm.8S w0, w0, w1

    /* Store the result back to DMEM. */
    bn.sid x0, 0(x4++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Pointwise Montgomery multiplication and subsequent addition of three
 * polynomials a(X), b(X), c(X) over Z_q[X] / (X^256 + 1) such that the result
 * is equal to a(X) * b(X) * R^-1 + c(X) mod q.
 *
 * Each a, b and c are assumed to be stored in 1024-byte (256 32-bit
 * coefficient slots) regions in DMEM. Depending on whether {x2, x3, x4} == x5,
 * this routine is either in-place or not.
 *
 * The caller must ensure that the modulus q and the corresponding Montgomery
 * multiplication constant have been correctly prepared (see the `MOD` register
 * and usage of the `bn.{add,sub,mul}vm` instructions) prior to invoking this
 * routine.
 *
 * CAUTION: The coefficients of a(X), b(X), c(X) are not mapped into the
 * Montgomery space nor are the output coefficients converted back. It is the
 * responsibility of the caller to appropriately adjust the input/output
 * polynomials. For example, if two coefficients x and y are given as is, then
 * the resulting Montgomery mulplication will result in x * y * R^-1 mod q,
 * where R = 2^32.
 *
 * @param[in] x2: DMEM address of the polynomial a(X).
 * @param[in] x3: DMEM address of the polynomial b(X).
 * @param[in] x4: DMEM address of the polynomial c(X).
 * @param[in] x5: DMEM address of the result a(X) * b(X) * R^-1 + c(X) mod q.
 */
poly_mul_add:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* WDR pointers for the coefficients of b(X) and c(X). */
  addi x6, x0, 1
  addi x7, x0, 2

  /* Each iteration calculates the pointwise Montgomery multiplication
     and subsequent modular addition of 8 coefficients. */
  loopi 32, 7
    /* Load 8 coefficients of a(X), b(X) and c(X) into w0, w1 and w2. */
    bn.lid x0, 0(x2++)
    bn.lid x6, 0(x3++)
    bn.lid x7, 0(x4++)

    /* Execute the vectorized Montgomery multiplication. */
    bn.mulvm.8S w0, w0, w1
    bn.addvm.8S w0, w0, w31 /* cond sub */

    /* Execute the vectorized modular addition. */
    bn.addvm.8S w0, w0, w2

    bn.sid x0, 0(x5++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x7, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
