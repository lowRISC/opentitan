/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for ECDSA signature verification and curve point
 *   test.
 */

 .section .text

/**
 * Checks if a point is a valid curve point on curve P-384
 *
 * Returns r = x^3 + ax + b  mod p
 *     and s = y^2  mod p
 *         where x,y are the affine coordinates of the curve point and
 *              a, b and p being the domain parameters of curve P-384.
 *
 * This routine checks if a point with given x- and y-coordinate is a valid
 * curve point on P-384.
 * The routine checks whether the coordinates are a solution of the
 * Weierstrass equation y^2 = x^3 + ax + b  mod p.
 * The routine makes use of the property that the domain parameter 'a' can be
 * written as a=-3 for the P-384 curve, hence the routine is limited to P-384.
 * The routine does not return a boolean result but computes the left side
 * and the right sight of the Weierstrass equation and leaves the final
 * comparison to the caller.
 * The routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[12]: dptr_r, pointer to dmem location where right
 *                               side result r will be stored
 * @param[in]  dmem[16]: dptr_s, pointer to dmem location where left side
 *                               result s will be stored
 * @param[in]  dmem[20]: dptr_x, pointer to dmem location containing affine
 *                               x-coordinate of input point
 * @param[in]  dmem[24]: dptr_y, pointer to dmem location containing affine
 *                               y-coordinate of input point
 *
 * clobbered registers: x2, x3, w0 to w5, w10 to w17
 * clobbered flag groups: FG0
 */
 .globl p384_isoncurve
p384_isoncurve:

  /* setup all-zero reg */
  bn.xor    w31, w31, w31

  /* load affine x-coordinate of curve point from dmem
     [w1, w0] <= dmem[dptr_x] = dmem[20] */
  la        x3, dptr_x
  lw        x3, 0(x3)
  li        x2, 0
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load affine y-coordinate of curve point from dmem
     [w3, w2] <= dmem[dptr_y] = dmem[24] */
  la        x3, dptr_y
  lw        x3, 0(x3)
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* load domain parameter p (modulus) from dmem
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load domain parameter b from dmem
     [w4, w5] = b = dmem[p384_b] */
  li        x2, 4
  la        x3, p384_b
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* y^2 = [w17,w16] <= y*y = [w3,w2]*w[w3,w2] */
  bn.mov    w10, w2
  bn.mov    w11, w3
  bn.mov    w16, w2
  bn.mov    w17, w3
  jal       x1, p384_mulmod_p

  /* store result (left side): dmem[dptr_s] <= y^2 = [w17,w16] */
  la        x3, dptr_s
  lw        x3, 0(x3)
  li        x2, 16
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)

  /*  x^3 = [w17,w16] <= (x*x)*x = ([w1,w0]*(w1,w0])*[w1,w0] */
  bn.mov    w10, w0
  bn.mov    w11, w1
  bn.mov    w16, w0
  bn.mov    w17, w1
  jal       x1, p384_mulmod_p
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, p384_mulmod_p

  /* for curve P-384, 'a' can be written as a = -3, therefore we subtract
     x three times from x^3.
     x^3 + ax  mod p = [w17,w16] <= x^3 -3 x mod p
                     = [w17,w16] - [w1,w0] - [w1,w0] - [w1,w0] mod [w13,w12] */
  loopi     3, 6
    bn.sub    w16, w16, w0
    bn.subb   w17, w17, w1
    bn.add    w10, w16, w12
    bn.addc   w11, w17, w13
    bn.sel    w16, w10, w16, C
    bn.sel    w17, w11, w17, C

  /* add domain parameter b
     x^3 + ax + b mod p = [w17,w16] <= [w17,w16] + [w5,w4] mod [w13,w12] */
  bn.add    w16, w16, w4
  bn.addc   w17, w17, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C

  /* store result (right side)
     dmem[dptr_r] <= x^3 + ax + b mod p = [w17,w16] */
  la        x3, dptr_r
  lw        x3, 0(x3)
  li        x2, 16
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)

  ret

/**
 * Check if a provided curve point is valid.
 *
 * For a given curve point (x, y), check that:
 * - x and y are both fully reduced mod p
 * - (x, y) is on the P-384 curve.
 *
 * Note that, because the point is in affine form, it is not possible that (x,
 * y) is the point at infinity. In some other forms such as projective
 * coordinates, we would need to check for this also.
 *
 * This routine raises a software error and halts operation if the curve point
 * is invalid.
 *
 * @param[in]  dmem[12]: dptr_r, pointer to dmem location where right
 *                               side result r will be stored
 * @param[in]  dmem[16]: dptr_s, pointer to dmem location where left side
 *                               result s will be stored
 * @param[in]  dmem[20]: dptr_x, pointer to dmem location containing affine
 *                               x-coordinate of input point
 * @param[in]  dmem[24]: dptr_y, pointer to dmem location containing affine
 *                               y-coordinate of input point
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, x3, x20 to x23, w0 to w17
 * clobbered flag groups: FG0
 */
 .globl p384_curve_point_valid
p384_curve_point_valid:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Load public key x-coordinate.
     [w11, w10] <= dmem[x] = x */
  la        x20, dptr_x
  lw        x20, 0(x20)
  li        x2, 10
  bn.lid    x2++, 0(x20)
  bn.lid    x2, 32(x20)

  /* Compare x to p.
       FG0.C <= (x < p) */
  bn.sub    w0, w10, w12
  bn.subb   w0, w11, w13

  /* Trigger a fault if FG0.C is false. */
  csrrs     x2, FG0, x0
  andi      x2, x2, 1
  bne       x2, x0, _x_valid
  unimp

  _x_valid:

  /* Load public key y-coordinate.
       w2 <= dmem[y] = y */
  la        x21, dptr_y
  lw        x21, 0(x21)
  li        x2, 8
  bn.lid    x2++, 0(x21)
  bn.lid    x2, 32(x21)

  /* Compare y to p.
       FG0.C <= (y < p) */
  bn.sub    w0, w8, w12
  bn.subb   w0, w9, w13

  /* Trigger a fault if FG0.C is false. */
  csrrs     x2, FG0, x0
  andi      x2, x2, 1
  bne       x2, x0, _y_valid
  unimp

  _y_valid:

  /* Compute both sides of the Weierstrauss equation.
       dmem[r] <= (x^3 + ax + b) mod p
       dmem[s] <= (y^2) mod p */
  jal       x1, p384_isoncurve

  /* Load both sides of the equation.
       [w7, w6] <= dmem[r]
       [w5, w4] <= dmem[s] */
  la        x22, dptr_r
  lw        x22, 0(x22)
  li        x2, 6
  bn.lid    x2++, 0(x22)
  bn.lid    x2, 32(x22)
  la        x23, dptr_s
  lw        x23, 0(x23)
  li        x2, 4
  bn.lid    x2++, 0(x23)
  bn.lid    x2, 32(x23)

  /* Compare the two sides of the equation.
       FG0.Z <= (y^2) mod p == (x^2 + ax + b) mod p */
  bn.sub    w0, w4, w6
  bn.subb   w1, w5, w7

  bn.cmp    w0, w31

  /* Trigger a fault if FG0.Z is false. */
  csrrs     x2, FG0, x0
  srli      x2, x2, 3
  andi      x2, x2, 1
  bne       x2, x0, _pt_1st_reg_valid
  unimp
  unimp
  unimp

  _pt_1st_reg_valid:

  bn.cmp    w1, w31

  /* Trigger a fault if FG0.Z is false. */
  csrrs     x2, FG0, x0
  srli      x2, x2, 3
  andi      x2, x2, 1
  bne       x2, x0, _pt_valid
  unimp
  unimp
  unimp

  _pt_valid:

  ret

.data

/* Right side of Weierstrass equation */
.globl r
.balign 32
r:
  .zero 64

/* Left side of Weierstrass equation */
.globl s
.balign 32
s:
  .zero 64

/* Curve point x-coordinate. */
.globl x
.weak x
.balign 32
x:
  .zero 64

/* Curve point y-coordinate. */
.globl y
.weak y
.balign 32
y:
  .zero 64

/* pointer to R (dptr_r) */
.globl dptr_r
dptr_r:
  .zero 4

/* pointer to S (dptr_s) */
.globl dptr_s
dptr_s:
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
