/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial arithmetic operations for ML-KEM-1024 (q = 3329). */

.globl poly_add
.globl poly_sub
.globl poly_mul
.globl poly_mul_add

.text

/**
 * Pointwise Addition of polynomials for ML-KEM-1024.
 *
 * Computes c(X) = a(X) + b(X) mod 3329.
 *
 * @param[in]  x2: DMEM address of polynomial a(X) (256 32-bit words, 1024 bytes).
 * @param[in]  x3: DMEM address of polynomial b(X) (256 32-bit words, 1024 bytes).
 * @param[out] x4: DMEM address of polynomial c(X) (256 32-bit words, 1024 bytes).
 *
 * Clobbered WDRs: w0, w1.
 */
poly_add:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x2, x3, x4, x10
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  addi x10, x0, 1

  /* Loop 32 iterations (32 * 8 = 256 coefficients). */
  loopi 32, 4
    bn.lid x0, 0(x2++)
    bn.lid x10, 0(x3++)
    bn.addvm.8S w0, w0, w1
    bn.sid x0, 0(x4++)
    /* End of loop */

  /* Restore registers from stack. */
  .irp reg, x10, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Pointwise Subtraction of polynomials for ML-KEM-1024.
 *
 * Computes c(X) = a(X) - b(X) mod 3329.
 *
 * @param[in]  x2: DMEM address of polynomial a(X) (256 32-bit words, 1024 bytes).
 * @param[in]  x3: DMEM address of polynomial b(X) (256 32-bit words, 1024 bytes).
 * @param[out] x4: DMEM address of polynomial c(X) (256 32-bit words, 1024 bytes).
 *
 * Clobbered WDRs: w0, w1.
 */
poly_sub:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x2, x3, x4, x10
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  addi x10, x0, 1

  /* Loop 32 iterations (32 * 8 = 256 coefficients). */
  loopi 32, 4
    bn.lid x0, 0(x2++)
    bn.lid x10, 0(x3++)
    bn.subvm.8S w0, w0, w1
    bn.sid x0, 0(x4++)
    /* End of loop */

  /* Restore registers from stack. */
  .irp reg, x10, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Pointwise Montgomery Multiplication of NTT polynomials for ML-KEM-1024.
 *
 * Implements Algorithm 11 (MultiplyNTTs) and Algorithm 12 (BaseCaseMultiply) of FIPS 203.
 * Computes c(X) = a(X) * b(X) mod 3329 in the NTT domain. Evaluates 128 degree-1
 * polynomial multiplications modulo (X^2 - gamma_i).
 *
 * @param[in]  x2: DMEM address of polynomial a(X) (256 32-bit words, 1024 bytes).
 * @param[in]  x3: DMEM address of polynomial b(X) (256 32-bit words, 1024 bytes).
 * @param[in]  x4: DMEM address of duplicated gamma twiddles (256 32-bit words, 1024 bytes total).
 * @param[out] x5: DMEM output address for c(X) = a(X) * b(X) (256 32-bit words, 1024 bytes).
 *
 * Clobbered WDRs: w0, w1, w2, w3, w4, w5, w6, w8, w9, w10, w31.
 */
poly_mul:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x10, x11
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Setup WDR index registers for loop LID operations */
  addi x10, x0, 1
  addi x11, x0, 2

  /* Generate mask w9 = (0x00000000_ffffffff, ...) for selecting even slots */
  bn.not      w9, w31
  bn.trn1.8S  w9, w9, w31
  bn.not      w10, w9          /* w10 = mask for odd slots (0xffffffff_00000000, ...) */

  /* Loop 32 iterations processing 4 quadratic pairs (8 coefficients) per iteration. */
  loopi 32, 17
    /* Load 8 coefficients of a into w0, b into w1, and 4 duplicated twiddle pairs into w2. */
    bn.lid x0, 0(x2++)
    bn.lid x10, 0(x3++)
    bn.lid x11, 0(x4++)

    /* Basecase even products c0 = a0*b0 + a1*b1*gamma */
    bn.mulvm.8S w3, w0, w1
    bn.mulvm.8S w4, w3, w2
    bn.rshi     w5, w31, w4 >> 32
    bn.addvm.8S w5, w3, w5       /* w5[even] = c0 = a0*b0 + a1*b1*gamma */

    /* Basecase odd products c1 = a0*b1 + a1*b0 */
    bn.rshi     w6, w1, w1 >> 32 /* w6[even] = b1 */
    bn.mulvm.8S w3, w0, w6       /* w3[even] = a0*b1 */
    bn.rshi     w8, w31, w0 >> 32 /* w8[even] = a1 */
    bn.mulvm.8S w8, w8, w1       /* w8[even] = a1*b0 */
    bn.addvm.8S w8, w3, w8       /* w8[even] = c1 = a0*b1 + a1*b0 */

    /* Combine c0 (even) and c1 (odd) */
    bn.and      w5, w5, w9       /* clear odd slots of c0 */
    bn.rshi     w8, w8, w31 >> 224 /* move c1 to odd slots */
    bn.and      w8, w8, w10      /* clear even slots of c1 */
    bn.or       w0, w5, w8       /* w0 = [c7, c6, c5, c4, c3, c2, c1, c0] */

    /* Store 8 result coefficients back to DMEM[x5] */
    bn.sid      x0, 0(x5++)
    /* End of loop */

  /* Restore registers from stack. */
  .irp reg, x11, x10, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Pointwise Montgomery Multiply-Accumulate of NTT polynomials for ML-KEM-1024.
 *
 * Computes c_out(X) = c_in(X) + a(X) * b(X) mod 3329 in the NTT domain.
 * Fuses basecase multiplication and addition into a single pass. By using this
 * function instead of separate `poly_mul` and `poly_add` calls during matrix-vector
 * multiplication (e.g., A * s + e), it accumulates the product term directly into
 * the running total in WDR registers, eliminating temporary DMEM buffers and extra
 * memory read/write passes.
 * The _basemul_twiddles are stored in mlkem1024_ntt.
 *
 * @param[in]  x2: DMEM address of polynomial a(X) (256 32-bit words, 1024 bytes).
 * @param[in]  x3: DMEM address of polynomial b(X) (256 32-bit words, 1024 bytes).
 * @param[in]  x4: DMEM address of duplicated gamma twiddles (256 32-bit words, 1024 bytes).
 * @param[in]  x5: DMEM address of input accumulator polynomial c_in(X) (256 32-bit words, 1024 bytes).
 * @param[out] x6: DMEM output address for c_out(X) = c_in(X) + a(X) * b(X) mod 3329 (256 32-bit words, 1024 bytes).
 *
 * Clobbered WDRs: w0, w1, w2, w3, w4, w5, w6, w8, w9, w10, w13, w14, w31.
 */
poly_mul_add:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6, x10, x11, x12
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Setup WDR index registers for loop LID operations */
  addi x10, x0, 1
  addi x11, x0, 2
  addi x12, x0, 13

  /* Generate mask w9 = (0x00000000_ffffffff, ...) for selecting even slots */
  bn.not      w9, w31
  bn.trn1.8S  w9, w9, w31
  bn.not      w10, w9          /* w10 = mask for odd slots (0xffffffff_00000000, ...) */

  /* Loop 32 iterations processing 4 quadratic pairs (8 coefficients) per iteration. */
  loopi 32, 21
    /* Load 8 coefficients of a into w0, b into w1, 4 duplicated twiddle pairs into w2, and c_in into w13. */
    bn.lid x0, 0(x2++)
    bn.lid x10, 0(x3++)
    bn.lid x11, 0(x4++)
    bn.lid x12, 0(x5++)

    /* Basecase even products c0 = a0*b0 + a1*b1*gamma + c0_in */
    bn.mulvm.8S w3, w0, w1
    bn.mulvm.8S w4, w3, w2
    bn.rshi     w5, w31, w4 >> 32
    bn.addvm.8S w5, w3, w5       /* w5[even] = a0*b0 + a1*b1*gamma */
    bn.addvm.8S w5, w5, w13      /* w5[even] = c0_out = (a0*b0 + a1*b1*gamma) + c0_in */

    /* Basecase odd products c1 = a0*b1 + a1*b0 + c1_in */
    bn.rshi     w6, w1, w1 >> 32 /* w6[even] = b1 */
    bn.mulvm.8S w3, w0, w6       /* w3[even] = a0*b1 */
    bn.rshi     w8, w31, w0 >> 32 /* w8[even] = a1 */
    bn.mulvm.8S w8, w8, w1       /* w8[even] = a1*b0 */
    bn.addvm.8S w8, w3, w8       /* w8[even] = a0*b1 + a1*b0 */
    bn.rshi     w14, w31, w13 >> 32 /* w14[even] = c1_in */
    bn.addvm.8S w8, w8, w14      /* w8[even] = c1_out = (a0*b1 + a1*b0) + c1_in */

    /* Combine c0_out (even) and c1_out (odd) */
    bn.and      w5, w5, w9       /* clear odd slots of c0_out */
    bn.rshi     w8, w8, w31 >> 224 /* move c1_out to odd slots */
    bn.and      w8, w8, w10      /* clear even slots of c1_out */
    bn.or       w0, w5, w8       /* w0 = [c7, c6, c5, c4, c3, c2, c1, c0] */

    /* Store 8 result coefficients back to DMEM[x6] */
    bn.sid      x0, 0(x6++)
    /* End of loop */

  /* Restore registers from stack. */
  .irp reg, x12, x11, x10, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
