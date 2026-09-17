/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for constant-time scalar multiplication.
 */

 .section .text

/**
 * Externally callable wrapper for P-384 scalar point multiplication
 *
 * Calculates R = d*P = d*(x_p, y_p)
 *         where R, P are valid P-384 curve points in affine coordinates,
 *         d is a 384-bit scalar.
 *         Both affine coordinates of R are arithmetically masked.
 * Returns the masked coordinates of R and the corresponding masks.
 *
 * Sets up context and calls the internal scalar multiplication routine.
 * This routine runs in constant time.
 *
 * @param[in]   dmem[x]: affine x-coordinate in dmem
 * @param[in]   dmem[y]: affine y-coordinate in dmem
 * @param[in]  dmem[d0]: 1st scalar share d0 in dmem
 * @param[in]  dmem[d1]: 2nd scalar share d1 in dmem
 * @param[out] dmem[ecdh_x0]: masked x coordinate of R
 * @param[out] dmem[ecdh_x1]: corresponding mask of the x coordinate
 * @param[out] dmem[ecdh_y0]: masked y coordinate of R
 * @param[out] dmem[ecdh_y1]: corresponding mask of the y coordinate
 *
 * 384-bit quantities have to be provided in dmem in little-endian format,
 * 512 bit aligned, with the highest 128 bit set to zero.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, x3, x9 to x13, x17 to x21, x26 to x30
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

  /* set dmem pointer to point to x-coordinate */
  la       x20, x

  /* set dmem pointer to point to y-coordinate */
  la       x21, y

  /* set dmem pointer to point to 1st scalar share d0 */
  la       x17, d0

  /* set dmem pointer to point to 2nd scalar share d1 */
  la       x19, d1

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

  /* scalar multiplication in projective space
     [w30:w25] <= (x, y, z) = k * P */
  jal       x1, scalar_mult_int_p384_reblind

  /* load the result of the scalar multiplication into memory for
     the projective is on curve check. */
  li        x2, 25
  la        x3, x
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)
  la        x3, y
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)

  /* store the z coordinate to scratchpad */
  bn.sid    x2++, 0(x30)
  bn.sid    x2++, 32(x30)

  /* check if the result is on the p384 curve */
  jal       x1, p384_isoncurve_proj_check

  /* Arithmetic masking:
   1. Generate random masks r_x and r_y
   2. Subtract masks from projective x and y coordinates
      (x, y, z) -> ((x - r_x) mod p,
                    (y - r_y) mod p,
                     z)
   3. Convert masked curve point back to affine
      form.
   4. Multiply masks with z^-1 for use in
      affine space. */

  /* Load domain parameter.
     [w13,w12] = dmem[p384_p] */
  li        x2, 12
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Mask the x coordinate.
     [w26,w25] <= x - r_x mod p
     dmem[ecdh_x1] <= r_x */
  la        x3, ecdh_x1
  jal       x1, p384_mask_coordinate

  /* Mask the y coordinate.
     [w28,w27] <= y - r_y mod p
     dmem[ecdh_y1] <= r_y */
  bn.mov    w2, w25
  bn.mov    w3, w26
  bn.mov    w25, w27
  bn.mov    w26, w28
  la        x3, ecdh_y1
  jal       x1, p384_mask_coordinate

  bn.mov    w27, w25
  bn.mov    w28, w26
  bn.mov    w25, w2
  bn.mov    w26, w3

  /* conversion into affine space
     [w1, w0] <= z^-1
     [w28:w25] <= (x, y) */
  jal       x1, proj_to_affine_p384

  /* Store the masked affine coordinates in dmem.
     dmem[ecdh_x0] <= [w26,w25] = x_a
     dmem[ecdh_y0] <= [w28,w27] = y_a */
  li        x2, 25
  la        x3, ecdh_x0
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)
  bn.sid    x2++, 128(x3)
  bn.sid    x2, 160(x3)

  /* Load domain parameter.
     [w13,w12] = dmem[p384_p] */
  li        x2, 12
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Multiply both masks with z^-1.
     dmem[ecdh_x1] <= r_x * z^-1 mod p = x1
     dmem[ecdh_y1] <= r_y * z^-1 mod p = y1 */
  loopi     2, 11
    /* [w11,w10] <= dmem[x3 + 64] = r
       [w17,w16] <= [w1,w0] = z^-1 */
    li        x2, 10
    bn.lid    x2++, 64(x3)
    bn.lid    x2, 96(x3)
    bn.mov    w16, w0
    bn.mov    w17, w1

    /* [w17, w16] <= r * z^-1 mod p */
    jal       x1, p384_mulmod_p

    /* Store affine mask in dmem.
       dmem[x3 + 64] <= [w17,w16] */
    li        x2, 16
    bn.sid    x2++, 64(x3)
    bn.sid    x2, 96(x3)
    addi      x3, x3, 128
    bn.xor    w31, w31, w31 /* dummy */

  ret

/**
 * Arithmetically mask a P-384 coordinate with a fresh random mask.
 *
 * Returns A = (c - r) mod p for a fresh random mask r < p and stores the mask
 * r to dmem.
 *
 * This routine runs in constant time.
 *
 * @param[in]           x3: dptr_r, pointer to dmem location for the mask
 * @param[in]    [w26,w25]: c, coordinate to mask, c < p
 * @param[in]    [w13,w12]: p, modulus
 * @param[in]          w31: all-zero
 * @param[out]   [w26,w25]: A, masked coordinate
 * @param[out] dmem[dptr_r]: r, mask
 *
 * clobbered registers: x2, w0, w1, w6 to w9, w16 to w24
 * clobbered flag groups: FG0
 */
p384_mask_coordinate:
  /* Fetch a fresh randomness for the mask.
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
     [w26,w25] = A <= [w26,w25] - [w19,w18] mod [w13,w12] = c - r mod p */

  /* [w9,w8] = A1 <= [w26,w25] - [w19,w18] = c - r */
  bn.sub    w8, w25, w18
  bn.subb   w9, w26, w19

  /* [w7,w6] = A2 <= [w9,w8] + [w13,w12] = A1 + p = c - r + p */
  bn.add    w6, w8, w12
  bn.addc   w7, w9, w13

  /* If c < r: [w26,w25] <= A2, else: [w26,w25] <= A1 */
  bn.sub    w0, w25, w18
  bn.subb   w1, w26, w19
  bn.sel    w25, w6, w8, FG0.C
  bn.sel    w26, w7, w9, FG0.C
  bn.sub    w31, w31, w31  /* dummy instruction to clear flags */

  /* Store the mask to dmem for later use.
     dmem[dptr_r] <= [w19,w18] = r */
  li        x2, 18
  bn.sid    x2++, 0(x3)
  bn.sid    x2, 32(x3)

  ret
