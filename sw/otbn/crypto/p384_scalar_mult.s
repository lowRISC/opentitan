/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for constant-time scalar multiplication.
 */

 .section .text

/**
 * Externally callable wrapper for P-384 scalar point multiplication
 *
 * Calculates R = k*P = k*(x_p, y_p)
 *         where R, P are valid P-384 curve points in affine coordinates,
 *         k is a 384-bit scalar.
 *         The x coordinate of R is arithmetically masked.
 * Returns the masked x coordinate of R and the corresponding mask.
 *
 * Sets up context and calls the internal scalar multiplication routine.
 * This routine runs in constant time.
 *
 * @param[in]   x20:     dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]   x21:     dptr_y, pointer to affine y-coordinate in dmem
 * @param[in]   x17:     dptr_k0, pointer to location in dmem containing
 *                                1st scalar share k0
 * @param[in]   x19:     dptr_k1, pointer to location in dmem containing
 *                                2nd scalar share k1
 * @param[out]  dmem[x]: masked x coordinate of R
 * @param[out]  dmem[y]: corresponding mask
 *
 * 384-bit quantities have to be provided in dmem in little-endian format,
 * 512 bit aligned, with the highest 128 bit set to zero.
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30
 *                      w0 to w30
 * clobbered flag groups: FG0
 */
.globl p384_scalar_mult
p384_scalar_mult:

  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* set dmem pointer to domain parameter b */
  la        x28, p384_b

  /* set dmem pointer to scratchpad */
  la        x30, scratchpad

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load domain parameter n (order of base point)
     [w11, w10] = n = dmem[p384_n] */
  li        x2, 10
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* scalar multiplication inprojective space
     [w30:w25] <= (x, y, z) = k * P */
  jal       x1, scalar_mult_int_p384

  /* Arithmetic masking:
   1. Generate a random mask r
   2. Subtract masks from projective x coordinate
      (x, y, z) -> ((x - r) mod p,
                     y,
                     z)
   3. Convert masked curve point back to affine
      form.
   4. Multiply mask with z^-1 for use in
      affine space. */

  /* Load domain parameter.
     [w13,w12] = dmem[p384_p] */
  li        x2, 12
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Fetch a fresh randomness for mask.
     [w20, w19, w18] <= URND() = r */
  bn.wsrr   w18, URND
  bn.wsrr   w19, URND
  bn.wsrr   w20, URND

  /* Reduce r mod p
     [w19, w18] <= [w20, w19, w18] mod [w13, w12] = r mod p */
  jal       x1, p384_reduce_p
  bn.mov    w18, w16
  bn.mov    w19, w17

  /* Arithmetic masking.
     [w26,w25] = A <= [w26,w25] - [w19,w18] mod [w13,w12] = x - r mod p */

  /* [w9,w8] = A1 <= [w26,w25] - [w19,w18] = x - r */
  bn.sub    w8, w25, w18
  bn.subb   w9, w26, w19

  /* [w7,w6] = A2 <= [w9,w8] + [w13,w12] = A1 + p = x - r + p */
  bn.add    w6, w8, w12
  bn.addc   w7, w9, w13

  /* If x < r: [w26,w25] <= A2, else: [w26,w25] <= A1 */
  bn.sub    w0, w25, w18
  bn.subb   w1, w26, w19
  bn.sel    w25, w6, w8, FG0.C
  bn.sel    w26, w7, w9, FG0.C

  /* Store mask to dmem for later use.
     y coordinate is not required afterwards and therefore can be used
     for the mask. */
  li        x2, 18
  bn.sid    x2++, 0(x21)
  bn.sid    x2, 32(x21)

  /* conversion into affine space
     [w1, w0] <= z^-1
     [w28:w25] <= (x, y) */
  jal       x1, proj_to_affine_p384

  /* Get modular inverse z^-1 of projective z coordinate
     and multiply the random masks with z^-1 to
     also convert them into affine space. */

  /* Load domain parameter.
     [w13,w12] = dmem[p384_p] */
  li        x2, 12
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Move previously stored mask r and z^-1 into input WDRs
     for multiplication. */
  li        x2, 10
  bn.lid    x2++, 0(x21)
  bn.lid    x2, 32(x21)
  bn.mov    w16, w0
  bn.mov    w17, w1

  /* Compute affine mask by modular multiplication of r and z^-1.
     [w17, w16] = r_a = r * z^-1 mod p */
  jal       x1, p384_mulmod_p

  /* Store result in dmem.
     y coordinate is not required afterwards and
     is therefore replaced by the affine mask r_a*/
  li        x2, 25
  bn.sid    x2++, 0(x20)
  bn.sid    x2, 32(x20)
  li        x2, 16
  bn.sid    x2++, 0(x21)
  bn.sid    x2, 32(x21)

  ret

/* scratchpad memory */
.section .data

/* 704 bytes of scratchpad memory */
.balign 32
scratchpad:
  .zero 704
