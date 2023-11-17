/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for constant-time base point multiplication.
 */

 .section .text

/**
 * Externally callable routine for P-384 base point multiplication
 *
 * returns Q = d (*) G
 *         where Q is a resulting valid P-384 curve point in affine
 *                   coordinates,
 *               G is the base point of curve P-384, and
 *               d is a 384-bit scalar.
 *
 * Sets up context and calls the internal scalar multiplication routine.
 * This routine runs in constant time.
 *
 * @param[in]  dmem[0]: dptr_d0, pointer to location in dmem containing
 *                      1st private key share d0
 * @param[in]  dmem[4]: dptr_d1, pointer to location in dmem containing
 *                      2nd private key share d1
 * @param[in]  dmem[20]: dptr_x, pointer to result buffer for x-coordinate
 * @param[in]  dmem[24]: dptr_y, pointer to result buffer for y-coordinate
 *
 * 384-bit quantities have to be provided in dmem in little-endian format,
 * 512 bit aligned, with the highest 128 bit set to zero.
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 correspond
 *        to the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30
 *                      w0 to w30
 * clobbered flag groups: FG0
 */
.globl p384_base_mult
p384_base_mult:

  /* set dmem pointer to x-coordinate of base point*/
  la        x20, p384_gx

  /* set dmem pointer to y-coordinate of base point */
  la        x21, p384_gy

  /* set dmem pointer to 1st scalar share d0 */
  la        x17, dptr_d0
  lw        x17, 0(x17)

  /* set dmem pointer to 2nd scalar share d1 */
  la        x19, dptr_d1
  lw        x19, 0(x19)

  /* set dmem pointer to domain parameter b */
  la        x28, p384_b

  /* set dmem pointer to scratchpad */
  la        x30, scratchpad

  /* load domain parameter n (order of base point)
     [w11, w10] = n = dmem[p384_n] */
  li        x2, 10
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* init all-zero reg */
  bn.xor    w31, w31, w31

  /* scalar multiplication in projective space
     [w30:w25] <= (x, y, z) = d * G */
  jal       x1, scalar_mult_int_p384

  /* conversion into affine space
     [w28:w25] <= (x, y) */
  jal       x1, proj_to_affine_p384

  /* set dmem pointer to point x-coordinate */
  la        x20, dptr_x
  lw        x20, 0(x20)

  /* set dmem pointer to point y-coordinate */
  la        x21, dptr_y
  lw        x21, 0(x21)

  /* store result in dmem */
  li        x2, 25
  bn.sid    x2++, 0(x20)
  bn.sid    x2++, 32(x20)
  bn.sid    x2++, 0(x21)
  bn.sid    x2++, 32(x21)

  ret

/* pointers and scratchpad memory */
.section .data

.balign 32

  /* pointer to k0 (dptr_k0) */
.globl dptr_k0
.weak dptr_k0
dptr_k0:
  .zero 4

/* pointer to k1 (dptr_k1) */
.globl dptr_k1
.weak dptr_k1
dptr_k1:
  .zero 4

/* pointer to d0 (dptr_d0) */
.globl dptr_d0
.weak dptr_d0
dptr_d0:
  .zero 4

/* pointer to d1 (dptr_d1) */
.globl dptr_d1
.weak dptr_d1
dptr_d1:
  .zero 4

/* pointer to X (dptr_x) */
.globl dptr_x
.weak dptr_x
dptr_x:
  .zero 4

/* pointer to Y (dptr_y) */
.globl dptr_y
.weak dptr_y
dptr_y:
  .zero 4

/* 704 bytes of scratchpad memory */
.balign 32
.globl scratchpad
.weak scratchpad
scratchpad:
  .zero 704
