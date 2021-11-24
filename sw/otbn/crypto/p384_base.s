/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   This library contains:
 *   - P-384 specific routines for point addition in projective space
 *   - P-384 domain parameters
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
 * Flags: Flags have no meaning beyond the scope of this subroutine.
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
     carried out along the way. To add them in the q2 domain, they would have
     to be left shifted by 384 bit first. To directly add them we first shift
     q2' by 384 bit to the right, perform the additions, and shift the result
     another bit to the right. The additions cannot overflow due to leading
     zeros after shift.
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
     overflow due to leading zeros.
     q2'''' = x[767]?q2'''+u[383:0]:q2'''
            = [w20, w19] + [w24, w23] = q2 >> 384 */
  bn.add w19, w19, w23
  bn.addc w20, w20, w24
  /* finally this gives q3 by shifting the remaining bit to the right
     q3 = q2 >> 385 = q2'''' >> 1 = [w11, w10] = [w20, w19] >> 1 */
  bn.rshi w11, w31, w20 >> 1
  bn.rshi w10, w20, w19 >> 1

  /* r2 = q3*m[511:0] = [w17, w16] = ([w11, w10] * [w13, w12])[511:0]
     A 384x384 bit multiplication kernel is used here, hence both q3 and p
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
 * Flags: Flags have no meaning beyond the scope of this subroutine.
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


.section .data

/* P-384 domain parameter b */
.globl p384_b
p384_b:
  .word 0xd3ec2aef
  .word 0x2a85c8ed
  .word 0x8a2ed19d
  .word 0xc656398d
  .word 0x5013875a
  .word 0x0314088f
  .word 0xfe814112
  .word 0x181d9c6e
  .word 0xe3f82d19
  .word 0x988e056b
  .word 0xe23ee7e4
  .word 0xb3312fa7
  .zero 16

/* P-384 domain parameter p (modulus) */
.globl p384_p
p384_p:
  .word 0xffffffff
  .word 0x00000000
  .word 0x00000000
  .word 0xffffffff
  .word 0xfffffffe
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .zero 16

/* barrett constant u for modulus p */
.globl p384_u_p
p384_u_p:
  .word 0x00000001
  .word 0xffffffff
  .word 0xffffffff
  .word 0x00000000
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .zero 16

/* P-384 domain parameter n (order of base point) */
.globl p384_n
p384_n:
  .word 0xccc52973
  .word 0xecec196a
  .word 0x48b0a77a
  .word 0x581a0db2
  .word 0xf4372ddf
  .word 0xc7634d81
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .zero 16

/* barrett constant u for n */
.globl p384_u_n
p384_u_n:
  .word 0x333ad68d
  .word 0x1313e695
  .word 0xb74f5885
  .word 0xa7e5f24d
  .word 0x0bc8d220
  .word 0x389cb27e
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .zero 16

/* P-384 basepoint G affine x-coordinate */
.globl p384_gx
p384_gx:
  .word 0x72760ab7
  .word 0x3a545e38
  .word 0xbf55296c
  .word 0x5502f25d
  .word 0x82542a38
  .word 0x59f741e0
  .word 0x8ba79b98
  .word 0x6e1d3b62
  .word 0xf320ad74
  .word 0x8eb1c71e
  .word 0xbe8b0537
  .word 0xaa87ca22
  .zero 16

/* P-384 basepoint G affine y-coordinate */
.globl p384_gy
p384_gy:
  .word 0x90ea0e5f
  .word 0x7a431d7c
  .word 0x1d7e819d
  .word 0x0a60b1ce
  .word 0xb5f0b8c0
  .word 0xe9da3113
  .word 0x289a147c
  .word 0xf8f41dbd
  .word 0x9292dc29
  .word 0x5d9e98bf
  .word 0x96262c6f
  .word 0x3617de4a
  .zero 16
