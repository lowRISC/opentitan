/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for p384 is on curve check.
 */

 .section .text

/**
 * Checks if a point is a valid curve point on curve P-384.
 *
 * This routine checks if a point with given x-, y- and z-coordinates is a valid
 * curve point on P-384. To this end p384_isoncurve_proj is called to compute
 * both sides of the Weierstrass equation zy^2 = x^3 + axz^2 + bz^3  mod p.
 *
 * Finally, both sides of the equation are compared.
 * This routine sets `ok` to false if the check fails and immediately exits the
 * program. If the check succeeds, `ok` is unmodified.
 *
 * The routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w13, w12]:  domain parameter p (modulus)
 * @param[in]  x20:         dptr_x, pointer to dmem location containing projective
 *                                  x-coordinate of input point
 * @param[in]  x21:         dptr_y, pointer to dmem location containing projective
 *                                  y-coordinate of input point
 * @param[in]  x30:         dptr_sp, pointer to 704 bytes of scratchpad memory in dmem
 *
 * Scratchpad memory layout:
 * The routine expects at least 194 bytes of scratchpad memory at dmem
 * location 'scratchpad' (sp). Internally the scratchpad is used as follows:
 * dptr_sp     .. dptr_sp+63:   z-coordinate of input point, projective
 * dptr_sp+64  .. dptr_sp+127:  dptr_rhs, pointer to dmem location where right
 *                              side result will be stored
 * dptr_sp+128 .. dptr_sp+191:  dptr_lhs, pointer to dmem location where left
 *                              side result will be stored
 *
 * clobbered registers: x2, x3, w0 to w5, w10 to w17
 * clobbered flag groups: FG0
 */
 .globl p384_isoncurve_proj_check
p384_isoncurve_proj_check:

  addi      x22, x30, 64
  addi      x23, x22, 64

  jal       x1, p384_isoncurve_proj

  /* load result to WDRs for comparison */
  li        x2, 2
  bn.lid    x2++,  0(x22)
  bn.lid    x2++, 32(x22)
  bn.lid    x2++,  0(x23)
  bn.lid    x2++, 32(x23)

  /* Compare the two sides of the equation.
       FG0.Z <= (y^2) mod p == (x^2 + ax + b) mod p */
  bn.cmp    w4, w2
  /* Fail if FG0.Z is false. */
  jal       x1, trigger_fault_if_fg0_z

  bn.cmp    w5, w3
  /* Fail if FG0.Z is false. */
  jal       x1, trigger_fault_if_fg0_z

  ret

/**
 * Checks if a point is a valid curve point on curve P-384
 *
 * Returns rhs = x^3 + axz^2 + bz^3  mod p
 *     and lhs = zy^2  mod p
 *         where x,y,z are the projective coordinates of the curve point and
 *              a, b and p being the domain parameters of curve P-384.
 *
 * This routine checks if a point with given x-, y- and z-coordinates is a valid
 * curve point on P-384.
 * The routine checks whether the coordinates are a solution of the modified
 * Weierstrass equation zy^2 = x^3 + axz^2 + bz^3  mod p.
 * The routine makes use of the property that the domain parameter 'a' can be
 * written as a=-3 for the P-384 curve, hence the routine is limited to P-384.
 * The routine does not return a boolean result but computes the left side
 * and the right sight of the Weierstrass equation and leaves the final
 * comparison to the caller.
 * The routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w13, w12]:  domain parameter p (modulus)
 * @param[in]  x20:         dptr_x,   pointer to dmem location containing projective
 *                                    x-coordinate of input point
 * @param[in]  x21:         dptr_y,   pointer to dmem location containing projective
 *                                    y-coordinate of input point
 * @param[in]  x22:         dptr_rhs, pointer to dmem location where right
 *                                    side result will be stored
 * @param[in]  x23:         dptr_lhs, pointer to dmem location where left side
 *                                    result will be stored
 * @param[in]  x30:         dptr_z,   pointer to dmem location containing projective
 *                                    z-coordinate of input point
 *
 * clobbered registers: x2, x3, w0 to w5, w10 to w17
 * clobbered flag groups: FG0
 */
 .globl p384_isoncurve_proj
p384_isoncurve_proj:

  /* load domain parameter b from dmem
     [w4, w5] = b = dmem[p384_b] */
  li        x2, 4
  la        x3, p384_b
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load projective z-coordinate of curve point from dmem
     [w1, w0] <= dmem[dptr_z] = dmem[19] */
  li        x2, 0
  bn.lid    x2++, 0(x30)
  bn.lid    x2++, 32(x30)

  /* bz^3 = [w5,w4] <= z*(z*(z*b)) = [w1,w0]*([w1,w0]*([w1,w0]*[w3,w2])) */
  bn.mov    w10, w0
  bn.mov    w11, w1
  bn.mov    w16, w4
  bn.mov    w17, w5
  jal       x1, p384_mulmod_p
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, p384_mulmod_p
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, p384_mulmod_p
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* setup all-zero reg */
  bn.xor    w31, w31, w31

  /* load projective x-coordinate of curve point from dmem
     [w1, w0] <= dmem[dptr_x] = dmem[20] */
  li        x2, 0
  bn.lid    x2++, 0(x20)
  bn.lid    x2++, 32(x20)

  /* load projective y-coordinate of curve point from dmem
     [w3, w2] <= dmem[dptr_y] = dmem[24] */
  bn.lid    x2++, 0(x21)
  bn.lid    x2, 32(x21)

  /* y^2 = [w17,w16] <= y*y = [w3,w2]*w[w3,w2] */
  bn.mov    w10, w2
  bn.mov    w11, w3
  bn.mov    w16, w2
  bn.mov    w17, w3
  jal       x1, p384_mulmod_p

  /* load projective z-coordinate of curve point from dmem
     [w11, w10] <= dmem[dptr_z] = dmem[19] */
  li        x2, 10
  bn.lid    x2++, 0(x30)
  bn.lid    x2++, 32(x30)

  /* zy^2 = [w17,w16] <= z*y^2 = [w17,w16]*[w11,w10] */
  jal       x1, p384_mulmod_p

  /* store result (left side): dmem[dptr_lhs] <= zy^2 = [w17,w16] */
  li        x2, 16
  bn.sid    x2++, 0(x23)
  bn.sid    x2++, 32(x23)

  /* load projective z-coordinate of curve point from dmem
     [w11, w10] <= dmem[dptr_z] = dmem[19] */
  li        x2, 10
  bn.lid    x2++, 0(x30)
  bn.lid    x2++, 32(x30)

  /* xz = [w17,w16] <= z*x = [w11,w10]*[w1,w0] */
  bn.mov    w16, w0
  bn.mov    w17, w1
  jal       x1, p384_mulmod_p

  /* load projective z-coordinate of curve point from dmem
     [w11, w10] <= dmem[dptr_z] = dmem[19] */
  li        x2, 10
  bn.lid    x2++, 0(x30)
  bn.lid    x2++, 32(x30)

  /* xz^2 = [w3,w2] <= z*(z*x) = [w3,w2]*[w11,w10] */
  jal       x1, p384_mulmod_p
  bn.mov    w2, w16
  bn.mov    w3, w17

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
     xz^2 three times from x^3.
     x^3 + axz^2  mod p = [w17,w16] <= x^3 -3xz^2 mod p
                        = [w17,w16] - [w3,w2] - [w3,w2] - [w3,w2] mod [w13,w12] */
  loopi     3, 6
    bn.sub    w0,  w16, w2
    bn.subb   w1,  w17, w3
    bn.add    w10, w0,  w12
    bn.addc   w11, w1,  w13
    bn.sel    w16, w10, w0, C
    bn.sel    w17, w11, w1, C

  /* add domain parameter bz^3
     x^3 + axz^2 + bz^3 mod p = [w1,w0] <= [w17,w16] + [w5,w4] mod [w13,w12] */
  bn.add    w16, w16, w4
  bn.addc   w17, w17, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w0,  w16, w10, C
  bn.sel    w1,  w17, w11, C

  /* store result (right side)
     dmem[dptr_rhs] <= x^3 + axz^2 + bz^3 mod p = [w1,w0] */
  li        x2, 0
  bn.sid    x2++, 0(x22)
  bn.sid    x2++, 32(x22)

  ret
