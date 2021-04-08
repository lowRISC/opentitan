/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines
 */

 .section .text


/**
 * 384-bit modular multiplication based on Barrett reduction algorithm
 * optimized for the special modulus of the NIST P-384 curve.
 *
 * Returns c = a x b % p.
 *
 * Expects: two operands, modulus p and pre-calculated parameter u for barrett
 * reduction (usually greek mu in literature). u is expected without the
 * leading 1 at bit 384. u has to be pre-calculated as u = floor(2^768/p).
 *
 * This implementation mostly follows the description in the
 * "Handbook of Applied Cryptography" in Algorithm 14.42.
 * Differences:
 *   - This implementation incorporates a multiplication before the reduction.
 *     Therefore it expects two operands (a, b) instead of a wider integer x.
 *   - The computation of q2 ignores the MSbs of q1 and u to allow using
 *     a 384x384 bit multiplication. This is compensated later by
 *     individual (conditional) additions.
 *   - The truncations in step 2 of HAC 14.42 in the form of (... mod b^(k+1) )
 *     are not implemented here and the full register width is used. This
 *     allows to omit computation of r1 (since r1=x) and step 3 of HAC 14.42
 *
 * Flags: Flags when leaving this subroutine depend on a potentially discarded
 *        value and therefore are not usable after return.
 *
 * @param[in] [w11, w10]: a, first operand, max. length 384 bit, a < m.
 * @param[in] [w17, w16]: b, second operand, max. length 384 bit, b < m.
 * @param[in] [w13, w12]: p, modulus of P384 i.e.:
                             m = 2^384 - 2^128 - 2^96 + 2^32 - 1.
 * @param[in] [w15, w14]: u, pre-computed Barrett constant (without u[384]/MSb
 *                           of u which is always 1 for the allowed range but
 *                           has to be set to 0 here).
 * @param[in] w31: all-zero.
 * @param[out] [w17, w16]: c, result, max. length 384 bit.
 *
 * Clobbered registers: w10, w11, w16, w17, w18, w19, w20, w21, w22, w23, w24
 * Clobbered flag groups: FG0
 */
 .globl barrett384_p384
barrett384_p384:
  /* Compute the integer product of the operands x = a * b
     x = [w18, w22, w21] = a * b = [w11, w10] * [w17, w16]
     => max. length x: 768 bit */
  bn.mulqacc.z          w10.0, w16.0,   0
  bn.mulqacc            w10.0, w16.1,  64
  bn.mulqacc.so w21.L,  w10.1, w16.0,  64
  bn.mulqacc            w10.0, w16.2,   0
  bn.mulqacc            w10.1, w16.1,   0
  bn.mulqacc            w10.2, w16.0,   0
  bn.mulqacc            w10.0, w16.3,  64
  bn.mulqacc            w10.1, w16.2,  64
  bn.mulqacc            w10.2, w16.1,  64
  bn.mulqacc.so w21.U,  w10.3, w16.0,  64
  bn.mulqacc            w10.0, w17.0,   0
  bn.mulqacc            w10.1, w16.3,   0
  bn.mulqacc            w10.2, w16.2,   0
  bn.mulqacc            w10.3, w16.1,   0
  bn.mulqacc            w11.0, w16.0,   0
  bn.mulqacc            w10.0, w17.1,  64
  bn.mulqacc            w10.1, w17.0,  64
  bn.mulqacc            w10.2, w16.3,  64
  bn.mulqacc            w10.3, w16.2,  64
  bn.mulqacc            w11.0, w16.1,  64
  bn.mulqacc.so w22.L,  w11.1, w16.0,  64
  bn.mulqacc            w10.1, w17.1,   0
  bn.mulqacc            w10.2, w17.0,   0
  bn.mulqacc            w10.3, w16.3,   0
  bn.mulqacc            w11.0, w16.2,   0
  bn.mulqacc            w11.1, w16.1,   0
  bn.mulqacc            w10.2, w17.1,  64
  bn.mulqacc            w10.3, w17.0,  64
  bn.mulqacc            w11.0, w16.3,  64
  bn.mulqacc.so w22.U,  w11.1, w16.2,  64
  bn.mulqacc            w10.3, w17.1,   0
  bn.mulqacc            w11.0, w17.0,   0
  bn.mulqacc            w11.1, w16.3,   0
  bn.mulqacc            w11.0, w17.1,  64
  bn.mulqacc.so w18.L,  w11.1, w17.0,  64
  bn.mulqacc.so w18.U,  w11.1, w17.1,   0

  /* Store correction factor to compensate for later neglected MSb of x.
     x is 768 bit wide and therefore the 383 bit right shifted version q1
     (below) contains 385 bit. Bit 384 of q1 is neglected to allow using a
     384x384 multiplier. For the MSb of x being set we temporary store u
     (or zero) here to be used in a later constant time correction of a
     multiplication with u. Note that this requires the MSb flag being carried
     over from the multiplication routine. */
  bn.sel w23, w14, w31, M
  bn.sel w24, w15, w31, M

  /* Compute q1 = x >> 383
     q1 = [w11, w10] = [w18, w22, w21] >> 383  = [w18, w21] >> 127
     => max length q1: 385 bits */
  bn.rshi w11, w31, w18 >> 127
  bn.rshi w10, w18, w22 >> 127

  /* Compute q2 = q1*u
     Instead of full q2 (which would be up to 770 bits) we ignore the MSb of u
     and the MSb of q1 and correct this later. This allows using a 384x384
     multiplier. We use the property that u for the modulus of P384 is zero in
     the bits 383 downto 129 and use a 384x192 multiplication routine.
     => max. length q2': 513 bit
     q2' = q1[383:0]*u[128:0] = [w18, w17, w16] = [w11, w10] * [w15, w14] */

  /* 576 = 384*192 bit multiplication kernel */
  bn.mulqacc.z          w10.0, w14.0,   0
  bn.mulqacc            w10.0, w14.1,  64
  bn.mulqacc.so w16.L,  w10.1, w14.0,  64
  bn.mulqacc            w10.0, w14.2,   0
  bn.mulqacc            w10.1, w14.1,   0
  bn.mulqacc            w10.2, w14.0,   0
  bn.mulqacc            w10.1, w14.2,  64
  bn.mulqacc            w10.2, w14.1,  64
  bn.mulqacc.so w16.U,  w10.3, w14.0,  64
  bn.mulqacc            w10.2, w14.2,   0
  bn.mulqacc            w10.3, w14.1,   0
  bn.mulqacc            w11.0, w14.0,   0
  bn.mulqacc            w10.3, w14.2,  64
  bn.mulqacc            w11.0, w14.1,  64
  bn.mulqacc.so w17.L,  w11.1, w14.0,  64
  bn.mulqacc            w11.0, w14.2,   0
  bn.mulqacc            w11.1, w14.1,   0
  bn.mulqacc.so w17.U,  w11.1, w14.2,  64

  /* w14.3 is always zero here due to structure of Barrett constant */
  bn.mulqacc.wo w18,    w11.1, w14.3,  64

  /* q3 = q2 >> 385
     In this step, the compensation for the neglected MSbs of q1 and u is
     carried out underway. To add them in the q2 domain, they would have to be
     left shifted by 384 bit first. To directly add them we first shift q2' by
     384 bit to the right, perform the additions, and shift the result another
     bit to the right. The additions cannot overflow due to leading zeros
     after shift.
     q2'' = q2' >> 384 = [w20, w19] = [w18, w17, w16] >> 384
                                    = [w18, w17] >> 128 */
  bn.rshi w20, w31, w18 >> 128
  bn.rshi w19, w18, w17 >> 128
  /* Add q1. This is unconditional since MSb of u is always 1.
     This cannot overflow due to leading zeros.
     q2''' = q2'' + q1 = [w20, w19] = [w20, w19] + [w10, w11] */
  bn.add w19, w19, w10
  bn.addc w20, w20, w11
  /* Conditionally add u (without leading 1) in case of MSb of x being set.
     This is the "real" q2 but shifted by 384 bits to the right. This cannot
     overflow due to leading zeros
     q2'''' = x[767]?q2'''+u[383:0]:q2'''
            = [w20, w19] + [w24, w23] = q2 >> 384 */
  bn.add w19, w19, w23
  bn.addc w20, w20, w24
  /* finally this gives q3 by shifting the remaining bit to the right
     q3 = q2 >> 385 = q2'''' >> 1 = [w11, w10] = [w20, w19] >> 1 */
  bn.rshi w11, w31, w20 >> 1
  bn.rshi w10, w20, w19 >> 1

  /* r2 = q3*m[511:0] = [w17, w16] = ([w11, w10] * [w13, w12])[511:0]
     A 384x384 bit multiplication kernel is used here, hence both q3 or p
     must not be wider than 384 bit. This is always the case for p. For q3 it
     is the case if a<p and b<p.
     The 256 highest bits of the multiplication result are not needed,
     so we do not compute them. */
  bn.mulqacc.z          w10.0, w12.0,   0
  bn.mulqacc            w10.0, w12.1,  64
  bn.mulqacc.so w16.L,  w10.1, w12.0,  64
  bn.mulqacc            w10.0, w12.2,   0
  bn.mulqacc            w10.1, w12.1,   0
  bn.mulqacc            w10.2, w12.0,   0
  bn.mulqacc            w10.0, w12.3,  64
  bn.mulqacc            w10.1, w12.2,  64
  bn.mulqacc            w10.2, w12.1,  64
  bn.mulqacc.so w16.U,  w10.3, w12.0,  64
  bn.mulqacc            w10.0, w13.0,   0
  bn.mulqacc            w10.1, w12.3,   0
  bn.mulqacc            w10.2, w12.2,   0
  bn.mulqacc            w10.3, w12.1,   0
  bn.mulqacc            w11.0, w12.0,   0
  bn.mulqacc            w10.0, w13.1,  64
  bn.mulqacc            w10.1, w13.0,  64
  bn.mulqacc            w10.2, w12.3,  64
  bn.mulqacc            w10.3, w12.2,  64
  bn.mulqacc            w11.0, w12.1,  64
  bn.mulqacc.so w17.L,  w11.1, w12.0,  64
  bn.mulqacc            w10.1, w13.1,   0
  bn.mulqacc            w10.2, w13.0,   0
  bn.mulqacc            w10.3, w12.3,   0
  bn.mulqacc            w11.0, w12.2,   0
  bn.mulqacc            w11.1, w12.1,   0
  bn.mulqacc            w10.2, w13.1,  64
  bn.mulqacc            w10.3, w13.0,  64
  bn.mulqacc            w11.0, w12.3,  64
  bn.mulqacc.so w17.U,  w11.1, w12.2,  64

  /* Compute r = x-r2 = x-q3*p
     since 0 <= r < 3*p, we only need to consider the lower limbs of x and r2
     r[511:0] = [w22, w21] - [w17, w16] */
  bn.sub w21, w21, w16
  bn.subb w22, w22, w17

  /* Barrett algorithm requires subtraction of the modulus at most two times if
     result is too large. However in the special case of P-384 we need to
     subtract only once */
  bn.sub w16, w21, w12
  bn.subb w17, w22, w13
  bn.sel w16, w21, w16, C
  bn.sel w17, w22, w17, C

  /* return result: c =[w17, w16] =  a * b % p. */
  ret


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
 * @param[in]  x26: dptr_p_p, dmem pointer to point P in dmem (projective)
 * @param[in]  x27: dptr_q_p, dmem pointer to point Q in dmem (projective)
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

  /* 19: [w30, w29] = Z3 <= b*t2 = dmem[x28+0]*[w5, w4] */
  bn.lid    x22, 0(x28)
  bn.lid    x23, 32(x28)
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

  /* 25: [w28, w27] = Y3 <= b*Y3 = dmem[x28+0]*[w28, w27] */
  bn.lid    x22, 0(x28)
  bn.lid    x23, 32(x28)
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


/**
 * Convert projective coordinates of a P-384 curve point to affine coordinates
 *
 * returns P = (x_a, y_a) = (x/z mod p, y/z mod p)
 *              where P is a valid P-384 curve point,
 *                    x_a and y_a are the resulting affine coordinates of the
 *                      curve point,
 *                    x,y and z are a set of projective coordinates of the
 *                      point and
 *                    p is the modulus of the P-384 underlying finite field.
 *
 * This routine computes the affine coordinates for a set of projective
 * coordinates of a valid P-384 curve point. The routine performs the required
 * divisions by computing the multiplicative modular inverse of the
 * projective z-coordinate in the underlying finite field of the P-384 curve.
 * For inverse computation Fermat's little theorem is used, i.e.
 * we compute z^-1 = z^(p-2) mod p.
 * For exponentiation a 16 step addition chain is used.
 * Source of the addition chain is the addchain project:
 * https://github.com/mmcloughlin/addchain/
 *
 * Flags: Flags when leaving this subroutine depend on a potentially discarded
 *        value and therefore are not usable after return.
 *
 * @param[in]  [w26,w25]: x, x-coordinate of curve point (projective).
 * @param[in]  [w26,w25]: y, y-coordinate of curve point (projective).
 * @param[in]  [w30,w29]: z, z-coordinate of curve point (projective).
 * @param[in]  [w13, w12]: p, modulus of P-384.
 * @param[in]  [w15, w14]: u, pre-computed Barrett constant for p,
 *                            lower 384 bits, i.e. (2^(2*384) div p)[383:0].
 * @param[in] w31: all-zero.
 * @param[out] [w26, w25]: x_a, affine x-coordinate of resulting point.
 * @param[out] [w28, w27]: y_a, affine y-coordinate of resulting point.
 *
 * clobbered registers: w0 to w28
 * clobbered flag groups: FG0
 */
proj_to_affine_p384:

  /* Exp: 0b10 = 2*0b1
     Val: r10 = z^2 mod p
          [w17,w16] <= [w30,w29]^2 mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  bn.mov    w16, w29
  bn.mov    w17, w30
  jal       x1, barrett384_p384

  /* Exp: 0b11 = 0b1+0b10
     Val: r11 <= z*r10 mod p
          [w17,w16] <= [w30,w29]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, barrett384_p384

  /* Exp: 0b110 = 2*0b11
     Val: r110 = r11^2 mod p
          [w17,w16] <= [w17,w16]^2 mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, barrett384_p384

  /* Exp: 0b111 = 0b1+0b110
     Val: r111 <= z*r110  mod p
          [w1,w0] = [w17,w16] <= [w30,w29]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, barrett384_p384
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* Exp: 0b111000 = 0b111<<3
     Val: r111000 <= r111^(2^3)  mod p
          [w17,w16] <= [w17,w16]^(2^3) mod [w13,w12] */
  loopi     3, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop

  /* Exp: 0b1111111 = 0b111+0b111000
     Val: r1111111 <= r111*r111000 mod p
          [w3,w2] = [w17,w16] <= [w1,w0]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, barrett384_p384
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* Exp: 2^12-1 = (0b1111111<<6)+0b111111
     Val: r_12_1 <= r111111^(2^6)*r111111 mod p
          [w5,w4] = [w17,w16] <= [w17,w16]^(2^6)*[w17,w16] mod [w13,w12] */
  loopi     6, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, barrett384_p384
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* Exp: 2^24-1 = ((2^12-1)<<12)+(2^12-1)
     Val: r_24_1 <= r_12_1^(2^12)*r12_1 mod p
          [w17,w16] <= [w17,w16]^(2^12)*[w5,w4] mod [w13,w12] */
  loopi     12, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w4
  bn.mov    w11, w5
  jal       x1, barrett384_p384

  /* Exp: 2^30-1 = ((2^24-1)<<6)+0b111111
     Val: r_30_1 <= r_24_1^(2^6)*r111111 mod p
          [w3, w2] = [w17,w16] <= [w17,w16]^(2^6)*[w3,w2] mod [w13,w12] */
  loopi     6, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, barrett384_p384
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* Exp: 2^31-1 <= (2^30-1)*2+0b1
     Val: r_31_1 <= r30_1^2*z mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^2*[w30,w29] mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, barrett384_p384
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, barrett384_p384
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* Exp: 2^32-1 <= (2^30-1)*2+0b1
     Val: r_32_1 <= r31_1^2*z mod p
          [w9,w8] = [w17,w16] <= [w17,w16]^2*[w30,w29] mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, barrett384_p384
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, barrett384_p384
  bn.mov    w9, w16
  bn.mov    w8, w17

  /* Exp: 2^63-1 <= ((2^32-1)<<31)+(2^31-1)
     Val: r_63_1 <= r_32_1^(2^31)*r_31_1 mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^(2^31)*[w7,w6] mod [w13,w12] */
  loopi     31, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, barrett384_p384
  bn.mov    w6, w16
  bn.mov    w7,w17

  /* Exp: 2^126-1 = ((2^63-1)<<63) + (2^63-1)
     Val: r_126_1 <= r_63_1^(2^63)*r_63_1 mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^(2^63)*[w7,w6] mod [w13,w12] */
  loopi     63, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, barrett384_p384
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* Exp: 2^252-1 = ((2^126-1)<<126)+(2^126-1)
     Val: r_252_1 <= r_126_1^(2^63)*r_126_1 mod p
          [w17,w16] <= [w17,w16]^(2^126)*[w7,w6] mod [w13,w12] */
  loopi     126, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, barrett384_p384

  /* Exp: 2^255-1 = ((2^252-1)<<3)+0b111
     Val: r_255_1 <= r_252_1^(2^3)*r111 mod p
          [w17,w16] <= [w17,w16]^(2^3)*[w1,w0] mod [w13,w12] */
  loopi     3, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, barrett384_p384

  /* Exp: p-2 = ((((((2^255-1)<<33)+(2^32-1))<<94)+(2^30-1))<<2)+0b1
     Val: x_inv <=((r_255_1^(2^33)*r_32_1)^(2^94)*r_30_1)^(2^2)*z mod p
          [w17,w16] <= (([w17,w16]^(2^33)*[w9,w8])^(2^94)*[w3,w2])^(2^2)
                       *[w30,w29] mod [w13,w12] */
  loopi     33, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w9
  bn.mov    w11, w8
  jal       x1, barrett384_p384
  loopi     94, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, barrett384_p384
  loopi     2, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, barrett384_p384
    nop
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, barrett384_p384

  /* store inverse [w1,w0] <= [w17,w16] = z_inv*/
  bn.mov w0, w16
  bn.mov w1, w17

  /* convert x-coordinate to affine space
     [w26,w25] <= [w17,w16] = x_a <= x/z = x*z_inv = [w26,w25]*[w1,w0] mod p */
  bn.mov    w10, w25
  bn.mov    w11, w26
  jal       x1, barrett384_p384
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* convert y-coordinate to affine space
     [w28,w27] <= [w17,w16] = y_a <= y/z = y*z_inv = [w28,w27]*[w1,w0] mod p */
  bn.mov    w10, w27
  bn.mov    w11, w28
  bn.mov    w16, w0
  bn.mov    w17, w1
  jal       x1, barrett384_p384
  bn.mov    w27, w16
  bn.mov    w28, w17

  ret


/**
 * Fetch curve point from dmem, randomize z-coordinate and store point in dmem
 *
 * returns P = (x, y, z) = (x_a*z, y_a*z, z)
 *         with P being a valid P-384 curve point in projective coordinates
 *              x_a and y_a being the affine coordinates as fetched from dmem
 *              z being a randomized z-coordinate
 *
 * This routines fetches the affine x- and y-coordinates of a curve point from
 * dmem and computes a valid set of projective coordinates. The z-coordinate is
 * randomized and x and y are scaled appropriately. The resulting projective
 * coordinates are stored at dmem[dptr_p_p] using 6 consecutive 256-bit cells,
 * i.e. each coordinate is stored 512 bit aligned, little endian.
 * This routine runs in constant time.
 *
 * @param[in]  x20: dptr_x, pointer to dmem location containing affine
 *                          x-coordinate of input point
 * @param[in]  x21: dptr_y, pointer to dmem location containing affine
 *                          y-coordinate of input point
 * @param[in]  [w15, w14]: u[383:0] lower 384 bit of Barrett constant u for
 *                                    modulus p
 * @param[in]  [w13, w12]: p, modulus of P-384 underlying finite field
 * @param[in]  w31: all-zero
 * @param[in]  x18: dptr_p_p, pointer to dmem location to store resulting point
 *                            in projective space
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the upper limb of projective y-coordinate.
 *
 * clobbered registers: x10, x11 to x13
  *                     w2, w3, w8 to w11, w16 to w24, w29, w30
 * clobbered flag groups: FG0
 */
store_proj_randomize:

  /* get a 384-bit random number
    [w3, w2] = random(384) */
  bn.wsrr   w2, 1
  bn.wsrr   w3, 1
  bn.rshi   w3, w31, w3 >> 128

  /* reduce random number
     [w2, w3] = z <= [w2, w3] mod p */
  bn.sub   w10, w2, w12
  bn.subb  w11, w3, w13
  bn.sel   w2, w2, w10, C
  bn.sel   w3, w3, w11, C

  bn.mov w10, w2
  bn.mov w11, w3

  /* store z-coordinate
     dmem[x20+128] = [w10, w11] */
  li        x10, 10
  li        x11, 11
  bn.sid    x10, 128(x18)
  bn.sid    x11, 160(x18)

  /* fetch x-coordinate from dmem
     [w16, w17] = x <= [dmem[dptr_x], dmem[dptr_x+32]] */
  li x12, 16
  li x13, 17
  bn.lid    x12,  0(x20)
  bn.lid    x13, 32(x20)

  /* scale and store x-coordinate
     [dmem[dptr_p_p], dmem[dptr_p_p+32]] = [w17, w16] =
       x_p <= [w11, w10] * [w17, w16] = z*x  mod p */

  jal       x1, barrett384_p384
  bn.sid    x12,  0(x18)
  bn.sid    x13, 32(x18)

  /* fetch y-coordinate from dmem
     [w11, w10] = x <= [dmem[dptr_y], dmem[dptr_y+32]] */
  bn.lid    x12,  0(x21)
  bn.lid    x13, 32(x21)

  /* scale and store y-coordinate
     [dmem[dptr_p_p+64], dmem[dptr_p_p+96]] = [w17, w16] =
       y_p <= [w11, w10] * [w17, w16] = z*y  mod p */
  bn.mov w10, w2
  bn.mov w11, w3
  jal       x1, barrett384_p384
  bn.sid    x12, 64(x18)
  bn.sid    x13, 96(x18)

  ret


/**
 * P-256 scalar point multiplication in affine space
 *
 * returns R = d*P = d*(x_p, y_p)
 *         where R, P are valid P-256 curve points in affine coordinates,
 *               d is a 256-bit scalar.
 *
 * This routine performs scalar multiplication based on the group laws
 * of Weierstrass curves.
 * A constant time double-and-add algorithm (sometimes referred to as
 * double-and-add-always) is used.
 * Due to the P-384 optimized implementations of the internally called routines
 * for point addition and doubling, this routine is limited to P-384 curves.
 * The routine makes use of blinding by additive splitting the
 * exponent/scalar d into two shares. The double-and-add loop operates on both
 * shares in parallel applying Shamir's trick.
 *
 * @param[in]  x9: dptr_rnd, pointer to location in dmem containing random
 *                           number to be used for additive splitting of scalar
 * @param[in]  x19: dptr_d, pointer to scalar d (0 < d < n) in dmem
 * @param[in]  x20: dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]  x21: dptr_y, pointer to affine y-coordinate in dmem
 * @param[in]  x28: dptr_b, pointer to domain parameter b of P-384 in dmem
 * @param[in]  x30: dptr_sp, pointer to 704 bytes of scratchpad memory in dmem
 * @param[in]  [w15, w14]: u[383:0] lower 384 bit of Barrett constant u
 *                                  corresponding to modulus p
 * @param[in]  [w13, w12]: p, modulus of P-384 underlying finite field
 * @param[in]  [w11, w10]: n, domain parameter of P-384 curve
 *                            (order of basepoint G)
 * @param[in]  w31: all-zero
 * @param[out] [w26, w25]: x_a, affine x-coordinate of resulting point R.
 * @param[out] [w28, w26]: y_a, affine y-coordinate of resulting point R.
 *
 * Scratchpad memory layout:
 * The routine expects at least 704 bytes of scratchpad memory at dmem
 * location dptr_sp. Internally the scratchpad is used as follows:
 * dptr_sp     .. dptr_sp+192: point P, projective
 * dptr_sp+192 .. dptr_sp+255: s0, 1st share of scalar
 * dptr_sp+256 .. dptr_sp+447: point 2P, projective
 * dptr_sp+448 .. dptr_sp+511: s1, 2nd share of scalar
 * dptr_sp+512 .. dptr_sp+703: point Q, projective
 *
 * Projective coordinates of a point are kept in dmem in little endian format
 * with the individual coordinates 512 bit aligned. The coordinates are stored
 * in x,y,z order (i.e. x at lowest, z at highest address). Thus, a 384 bit
 * curve point occupies 6 consecutive 256-bit dmem cells.
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x10, x11 to x13, x18, x26, x27, w0 to w30
 * clobbered flag groups: FG0
 */
.globl scalar_mult_int_p384
scalar_mult_int_p384:

  /* set regfile pointers to in/out regs of Barrett routine. Set here to avoid
     resetting in very call to point addition routine */
  li        x22, 10
  li        x23, 11
  li        x24, 16
  li        x25, 17

  /* fetch externally supplied random number from dmem
     [w1, w0] = dmem[dptr_rnd] = [dmem[x9], dmem[x9+32]] = rnd */
  li        x2, 0
  bn.lid    x2++, 0(x9)
  bn.lid    x2++, 32(x9)

  /* 1st share (reduced rnd)
     s0 = [w1, w0] <= rnd mod n = [w1, w0] mod [w11, w10] */
  bn.sub    w9, w0, w10
  bn.subb   w8, w1, w11
  bn.sel    w0, w0, w9, C
  bn.sel    w1, w1, w8, C

  /* load scalar d from dmem
     [w3, w2] = d <= dmem[dptr_d] = [dmem[x19], dmem[x19+32]] */
  bn.lid    x2++, 0(x19)
  bn.lid    x2, 32(x19)

  /* 2nd share (d-s0)
     s1 = [w3, w2] <= d - s0 mod n = [w2, w3] - [w1, w0] mod [w11, w10] */
  bn.sub    w2, w2, w0
  bn.subb   w3, w3, w1
  bn.add    w8, w2, w10
  bn.addc   w9, w3, w11
  bn.sel    w2, w8, w2, C
  bn.sel    w3, w9, w3, C

  /* left align both shares for probing of MSB in loop body */
  bn.rshi   w1, w1, w0 >> 128
  bn.rshi   w0, w0, w31 >> 128
  bn.rshi   w3, w3, w2 >> 128
  bn.rshi   w2, w2, w31 >> 128

   /* store shares in scratchpad */
  li        x2, 0
  bn.sid    x2++, 192(x30)
  bn.sid    x2++, 224(x30)
  bn.sid    x2++, 448(x30)
  bn.sid    x2++, 480(x30)

  /* get randomized projective coodinates of curve point
     P = (x_p, y_p, z_p) = dmem[dptr_sp] = (x*z mod p, y*z mod p, z) */
  add       x18, x30, 0
  jal       x1, store_proj_randomize

  /* double point P
     2P = ([w30,w29], [w28,w27], [w26, w25]) <= 2*P */
  add       x27, x30, x0
  add       x26, x30, x0
  jal       x1, proj_add_p384

  /* store point 2P in scratchpad @w30+256
     dmem[dptr_sc+256] = [w30:w25] = 2P */
  li        x2, 25
  bn.sid    x2++, 256(x30)
  bn.sid    x2++, 288(x30)
  bn.sid    x2++, 320(x30)
  bn.sid    x2++, 352(x30)
  bn.sid    x2++, 384(x30)
  bn.sid    x2++, 416(x30)

  /* init point Q = (0,1,0) for double-and-add in scratchpad */
  /* dmem[x26] = dmem[dptr_sc+512] = Q = (0,1,0) */
  addi      x26, x30, 512
  li        x2, 30
  bn.addi   w30, w31, 1
  bn.sid    x2++, 64(x26)
  bn.sid    x2, 0(x26)
  bn.sid    x2, 32(x26)
  bn.sid    x2, 96(x26)
  bn.sid    x2, 128(x26)
  bn.sid    x2, 160(x26)

  /* double-and-add loop with decreasing index */
  loopi     384, 85

    /* double point Q
       Q = ([w30,w29], [w28,w27], [w26, w25]) <= Q + dmem[x27] */
    add       x27, x26, x0
    jal       x1, proj_add_p384

    /* store Q in dmem
     dmem[x26] = dmem[dptr_sc+512] <= [w30:w25] */
    li        x2, 25
    bn.sid    x2++, 0(x26)
    bn.sid    x2++, 32(x26)
    bn.sid    x2++, 64(x26)
    bn.sid    x2++, 96(x26)
    bn.sid    x2++, 128(x26)
    bn.sid    x2++, 160(x26)

    /* Probe if MSb of either of the two scalars (rnd or d-rnd) but not both
       is 1.
       If only one MSb is set, select P for addition.
       If both MSbs are set, select 2P for addition.
       (If neither MSB is set, 2P will be selected but result discarded.) */
    li        x2, 0
    bn.lid    x2++, 224(x30)
    bn.lid    x2, 480(x30)
    bn.xor    w8, w0, w1
    /* Create conditional offeset into scratchpad.
       if (s0[512] xor s1[512]) x27 <= x30 else x27 <= x30+256 */
    csrrs     x3, 0x7c0, x0
    xori      x3, x3, -1
    andi      x3, x3, 2
    slli      x27, x3, 7
    add       x27, x27, x30

    /* Reload randomized projective coodinates for curve point P.
       P = (x_p, y_p, z_p) = dmem[dptr_sp] <= (x*z mod p, y*z mod p, z) */
    jal       x1, store_proj_randomize

    /* Add points Q+P or Q+2P depending on offset in x27.
       Q_a = ([w30,w29], [w28,w27], [w26, w25]) <= Q + dmem[x27] */
    jal       x1, proj_add_p384

    /* load shares from scratchpad
       [w1, w0] = s0; [w3, w2] = s1 */
    li        x2, 0
    bn.lid    x2++, 192(x30)
    bn.lid    x2++, 224(x30)
    bn.lid    x2++, 448(x30)
    bn.lid    x2++, 480(x30)

    /* M = s0[511] | s1[511] */
    bn.or     w8, w1, w3

    /* load q from scratchpad
        Q = ([w9,w8], [w7,w6], [w5,w4]) <= dmem[x26] */
    li        x2, 4
    bn.lid    x2++, 0(x26)
    bn.lid    x2++, 32(x26)
    bn.lid    x2++, 64(x26)
    bn.lid    x2++, 96(x26)
    bn.lid    x2++, 128(x26)
    bn.lid    x2++, 160(x26)

    /* select either Q or Q_a
       if M: Q = ([w30,w29], [w28,w27], [w26, w25]) <= Q else: Q <= Q_a */
    bn.sel    w25, w25, w4, M
    bn.sel    w26, w26, w5, M
    bn.sel    w27, w27, w6, M
    bn.sel    w28, w28, w7, M
    bn.sel    w29, w29, w8, M
    bn.sel    w30, w30, w9, M

    /* store Q in dmem
     dmem[x26] = dmem[dptr_sc+512] <= [w30:w25] */
    li        x2, 25
    bn.sid    x2++, 0(x26)
    bn.sid    x2++, 32(x26)
    bn.sid    x2++, 64(x26)
    bn.sid    x2++, 96(x26)
    bn.sid    x2++, 128(x26)
    bn.sid    x2++, 160(x26)

    /* left shift both shares
       s0 <= s0 << 1 ; s1 <= s1 << 1 */
    bn.add    w0, w0, w0
    bn.addc   w1, w1, w1
    bn.add    w2, w2, w2
    bn.addc   w3, w3, w3
    /* store both shares in scratchpad */
    li        x2, 0
    bn.sid    x2++, 192(x30)
    bn.sid    x2++, 224(x30)
    bn.sid    x2++, 448(x30)
    bn.sid    x2++, 480(x30)


    /* Get a fresh random number and scale the coordinates of 2P.
       (scaling each proj. coordinate by same factor results in same point) */

    /* get a 384-bit random number */
    bn.wsrr   w2, 1
    bn.wsrr   w3, 1
    bn.rshi   w3, w31, w3 >> 128

    /* reduce random number
      [w2, w3] = z <= [w2, w3] mod p */
    bn.sub    w10, w2, w12
    bn.subb   w11, w3, w13
    bn.sel    w2, w2, w10, C
    bn.sel    w3, w3, w11, C

    /* scale all coordinates in scratchpad */
    li        x2, 16
    li        x3, 17
    /* x-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 256(x30)
    bn.lid    x3, 288(x30)
    jal       x1, barrett384_p384
    bn.sid    x2, 256(x30)
    bn.sid    x3, 288(x30)
    /* y-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 320(x30)
    bn.lid    x3, 352(x30)
    jal       x1, barrett384_p384
    bn.sid    x2, 320(x30)
    bn.sid    x3, 352(x30)
    /* z-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 384(x30)
    bn.lid    x3, 416(x30)
    jal       x1, barrett384_p384
    bn.sid    x2, 384(x30)
    bn.sid    x3, 416(x30)

  /* convert coordinates to affine space */
  jal       x1, proj_to_affine_p384

  ret
