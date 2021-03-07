/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   Routines for P-384 point addition in projective space.
 */

 .section .text

/**
 * P-384 point addition in projective space
 *
 * returns R = (x_r, y_r, z_r) <= P+Q = (x_p, y_p, z_p) + (x_q, y_q, z_q)
 *         with R, P and Q being valid P-384 curve points
 *           in projective coordinates
 *
 * This routine adds two valid P-384 curve points in projective space.
 * Point addition is performed based on the complete formulas of Bosma and
 * Lenstra for Weierstrass curves as first published in [1] and
 * optimized in [2].
 * The implemented version follows Algorithm 4 of [2] which is an optimized
 * variant for Weierstrass curves with domain parameter 'a' set to a=-3.
 * Numbering of the steps below and naming of symbols follows the
 * terminology of Algorithm 4 of [2].
 * The routine is limited to P-384 curve points due to:
 *   - fixed a=-3 domain parameter
 *   - usage of a P-384 optimized Barrett multiplication kernel
 * This routine runs in constant time.
 *
 * [1] https://doi.org/10.1006/jnth.1995.1088
 * [2] https://doi.org/10.1007/978-3-662-49890-3_16
 *
 * @param[in]  x22: set to 10, pointer to in reg for Barrett routine
 * @param[in]  x23: set to 11, pointer to in reg for Barrett routine
 * @param[in]  x24: set to 16, pointer to in/out reg for Barrett routine
 * @param[in]  x25: set to 17, pointer to in/out reg for Barrett routine
 * @param[in]  x26: dptr_P, dmem pointer to point P in dmem
 * @param[in]  x27: dptr_P, dmem pointer to point Q in dmem
 * @param[in]  x28: dptr_b, dmem pointer to domain parameter b of P-384 in dmem
 * @param[in]  [w13, w12]: p, modulus of underlying field of P-384
 * @param[in]  [w15, w14]: u[383:0] lower 384 bit of Barrett constant u for
 *                                    modulus p
 * @param[in]  w31: all-zero.
 * @param[out]  [w26, w25]: x_r, x-coordinate of resulting point R
 * @param[out]  [w28, w27]: y_r, y-coordinate of resulting point R
 * @param[out]  [w30, w29]: z_r, z-coordinate of resulting point R
 *
 * Flags: When leaving this subroutine, flags of FG0 depend on an
 *        intermediate result and are not usable after return.
 *        FG1 is not modified in this subroutine.
 *
 * clobbered registers: w0 to w30
 * clobbered flag groups: FG0
 */

.globl proj_add_p384
proj_add_p384:
  /* mapping of parameters to symbols of [2] (Algorithm 4):
     X1 = x_p; Y1 = y_p; Z1 = z_p; X2 = x_q; Y2 = y_q; Z2 = z_q
     X3 = x_r; Y3 = y_r; Z3 = z_r */

  /* 1: [w1, w0] = t0 <= X1*X2 = dmem[x26+0]*dmem[x27+0] */
  bn.lid    x22, 0(x26)
  bn.lid    x23, 32(x26)
  bn.lid    x24, 0(x27)
  bn.lid    x25, 32(x27)
  jal       x1, barrett384_p384
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* 2: [w3, w2] = t1 <= Y1*Y2 = dmem[x26+64]*dmem[x27+64] */
  bn.lid    x22, 64(x26)
  bn.lid    x23, 96(x26)
  bn.lid    x24, 64(x27)
  bn.lid    x25, 96(x27)
  jal       x1, barrett384_p384
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 3: [w5, w4] = t2 <= Z1*Z2 = dmem[x26+128]*dmem[x27+128] */
  bn.lid    x22, 128(x26)
  bn.lid    x23, 160(x26)
  bn.lid    x24, 128(x27)
  bn.lid    x25, 160(x27)
  jal       x1, barrett384_p384
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* 4: [w7, w6] = t3 <= X1+Y1 = dmem[x26+0]+dmem[x26+64] */
  bn.lid    x22, 0(x26)
  bn.lid    x23, 32(x26)
  bn.lid    x24, 64(x26)
  bn.lid    x25, 96(x26)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* 5: [w9, w8] = t4 <= X2+Y2 = dmem[x27+0]+dmem[x27+64] */
  bn.lid    x22, 0(x27)
  bn.lid    x23, 32(x27)
  bn.lid    x24, 64(x27)
  bn.lid    x25, 96(x27)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* 6: [w7, w6] = t3 <= t3*t4 = [w7, w6]*[w9, w8] */
  bn.mov    w10, w6
  bn.mov    w11, w7
  bn.mov    w16, w8
  bn.mov    w17, w9
  jal       x1, barrett384_p384
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* 7: [w9, w8] = t4 <= t0+t1 = [w1, w0]+[w3, w2] */
  bn.add    w16, w0, w2
  bn.addc   w17, w1, w3
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* 8: [w7, w6] = t3 <= t3-t4 = [w7, w6]-[w9, w8] */
  bn.sub    w16, w6, w8
  bn.subb   w17, w7, w9
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* 9: [w9, w8] = t4 <= Y1+Z1 = dmem[x26+64]+dmem[x26+128] */
  bn.lid    x22, 64(x26)
  bn.lid    x23, 96(x26)
  bn.lid    x24, 128(x26)
  bn.lid    x25, 160(x26)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* 10: [w26, w25] = X3 <= Y2+Z2 = dmem[x27+64]+dmem[x27+128] */
  bn.lid    x22, 64(x27)
  bn.lid    x23, 96(x27)
  bn.lid    x24, 128(x27)
  bn.lid    x25, 160(x27)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 11: [w9, w8] = t4 <= t4*X3 = [w9, w8]*[w26, w25] */
  bn.mov    w10, w8
  bn.mov    w11, w9
  bn.mov    w16, w25
  bn.mov    w17, w26
  jal       x1, barrett384_p384
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* 12: [w26, w25] = X3 <= t1+t2 = [w3, w2]+[w5, w4] */
  bn.add    w16, w2, w4
  bn.addc   w17, w3, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 13: [w9, w8] = t4 <= t4-X3 = [w9, w8]-[w26, w25] */
  bn.sub    w16, w8, w25
  bn.subb   w17, w9, w26
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* 14: [w26, w25] = X3 <= X1+Z1 = dmem[x26+0]+dmem[x26+128] */
  bn.lid    x22, 0(x26)
  bn.lid    x23, 32(x26)
  bn.lid    x24, 128(x26)
  bn.lid    x25, 160(x26)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 15: [w28, w27] = Y3 <= X2+Z2 = dmem[x27+0]+dmem[x27+128] */
  bn.lid    x22, 0(x27)
  bn.lid    x23, 32(x27)
  bn.lid    x24, 128(x27)
  bn.lid    x25, 160(x27)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 16: [w26, w25] = X3 <= X3*Y3 = [w26, w25]*[w28, w27] */
  bn.mov    w10, w25
  bn.mov    w11, w26
  bn.mov    w16, w27
  bn.mov    w17, w28
  jal       x1, barrett384_p384
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 17: [w28, w27] = Y3 <= t0+t2 = [w1, w0]+[w5, w4] */
  bn.add    w16, w0, w4
  bn.addc   w17, w1, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 18: [w28, w27] = Y3 <= X3-Y3 = [w26, w25]-[w28, w27] */
  bn.sub    w16, w25, w27
  bn.subb   w17, w26, w28
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 19: [w30, w29] = Z3 <= b*t2 = dmem[x5+0]*[w5, w4] */
  bn.lid    x22, 0(x5)
  bn.lid    x23, 32(x5)
  bn.mov    w16, w4
  bn.mov    w17, w5
  jal       x1, barrett384_p384
  bn.mov    w29, w16
  bn.mov    w30, w17

  /* 20: [w26, w25] = X3 <= Y3-Z3 = [w28, w27]-[w30, w29] */
  bn.sub    w16, w27, w29
  bn.subb   w17, w28, w30
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 21: [w30, w29] = Z3 <= X3+X3 = [w26, w25]+[w26, w25] */
  bn.add    w16, w25, w25
  bn.addc   w17, w26, w26
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w29, w16
  bn.mov    w30, w17

  /* 22: [w26, w25] = X3 <= X3+Z3 = [w26, w25]+[w30, w29] */
  bn.add    w16, w25, w29
  bn.addc   w17, w26, w30
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 23: [w30, w29] = Z3 <= t1-X3 = [w3, w2]-[w26, w25] */
  bn.sub    w16, w2, w25
  bn.subb   w17, w3, w26
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w29, w16
  bn.mov    w30, w17

  /* 24: [w26, w25] = X3 <= t1+X3 = [w3, w2]+[w26, w25] */
  bn.add    w16, w2, w25
  bn.addc   w17, w3, w26
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 25: [w28, w27] = Y3 <= b*Y3 = dmem[x5+0]*[w28, w27] */
  bn.lid    x22, 0(x5)
  bn.lid    x23, 32(x5)
  bn.mov    w16, w27
  bn.mov    w17, w28
  jal       x1, barrett384_p384
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 26: [w3, w2] = t1 <= t2+t2 = [w5, w4]+[w5, w4] */
  bn.add    w16, w4, w4
  bn.addc   w17, w5, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 27: [w5, w4] = t2 <= t1+t2 = [w3, w2]+[w5, w4] */
  bn.add    w16, w2, w4
  bn.addc   w17, w3, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* 28: [w28, w27] = Y3 <= Y3-t2 = [w28, w27]-[w5, w4] */
  bn.sub    w16, w27, w4
  bn.subb   w17, w28, w5
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 29: [w28, w27] = Y3 <= Y3-t0 = [w28, w27]-[w1, w0] */
  bn.sub    w16, w27, w0
  bn.subb   w17, w28, w1
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 30: [w3, w2] = t1 <= Y3+Y3 = [w28, w27]+[w28, w27] */
  bn.add    w16, w27, w27
  bn.addc   w17, w28, w28
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 31: [w28, w27] = Y3 <= t1+Y3 = [w3, w2]+[w28, w27] */
  bn.add    w16, w2, w27
  bn.addc   w17, w3, w28
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 32: [w3, w2] = t1 <= t0+t0 = [w1, w0]+[w1, w0] */
  bn.add    w16, w0, w0
  bn.addc   w17, w1, w1
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 33: [w1, w0] = t0 <= t1+t0 = [w3, w2]+[w1, w0] */
  bn.add    w16, w2, w0
  bn.addc   w17, w3, w1
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* 34: [w1, w0] = t0 <= t0-t2 = [w1, w0]-[w5, w4] */
  bn.sub    w16, w0, w4
  bn.subb   w17, w1, w5
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* 35: [w3, w2] = t1 <= t4*Y3 = [w9, w8]*[w28, w27] */
  bn.mov    w10, w8
  bn.mov    w11, w9
  bn.mov    w16, w27
  bn.mov    w17, w28
  jal       x1, barrett384_p384
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 36: [w5, w4] = t2 <= t0*Y3 = [w1, w0]*[w28, w27] */
  bn.mov    w10, w0
  bn.mov    w11, w1
  bn.mov    w16, w27
  bn.mov    w17, w28
  jal       x1, barrett384_p384
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* 37: [w28, w27] = Y3 <= X3*Z3 = [w26, w25]*[w30, w29] */
  bn.mov    w10, w25
  bn.mov    w11, w26
  bn.mov    w16, w29
  bn.mov    w17, w30
  jal       x1, barrett384_p384
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 38: [w28, w27] = Y3 <= Y3+t2 = [w28, w27]+[w5, w4] */
  bn.add    w16, w27, w4
  bn.addc   w17, w28, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 39: [w26, w25] = X3 <= t3*X3 = [w7, w6]*[w26, w25] */
  bn.mov    w10, w6
  bn.mov    w11, w7
  bn.mov    w16, w25
  bn.mov    w17, w26
  jal       x1, barrett384_p384
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 40: [w26, w25] = X3 <= X3-t1 = [w26, w25]-[w3, w2] */
  bn.sub    w16, w25, w2
  bn.subb   w17, w26, w3
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w16, w10, w16, C
  bn.sel    w17, w11, w17, C
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 41: [w30, w29] = Z3 <= t4*Z3 = [w9, w8]*[w30, w29] */
  bn.mov    w10, w8
  bn.mov    w11, w9
  bn.mov    w16, w29
  bn.mov    w17, w30
  jal       x1, barrett384_p384
  bn.mov    w29, w16
  bn.mov    w30, w17

  /* 42: [w3, w2] = t1 <= t3*t0 = [w7, w6]*[w1, w0] */
  bn.mov    w10, w6
  bn.mov    w11, w7
  bn.mov    w16, w0
  bn.mov    w17, w1
  jal       x1, barrett384_p384
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 43: [w30, w29] = Z3 <= Z3+t1 = [w30, w29]+[w3, w2] */
  bn.add    w16, w29, w2
  bn.addc   w17, w30, w3
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w16, w16, w10, C
  bn.sel    w17, w17, w11, C
  bn.mov    w29, w16
  bn.mov    w30, w17

ret
