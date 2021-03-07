/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   Constant time 384 bit modular multiplication based on Barrett reduction
 *   algorithm.
 *
 *   Provides a modular multiplication kernel for 384 bit wide numbers
 *   for the modulus and barret constant of NIST curve P384 only.
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
 * Clobbered registers: w16, w17, w18, w19, w20, w21, w22, w23, w24
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
