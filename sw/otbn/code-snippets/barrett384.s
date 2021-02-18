/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   Constant time 384 bit modular multiplication based on Barrett reduction
 *   algorithm.
 *
 *   Provides a generic modular multiplication kernel for 384 bit wide numbers
 *   without requiring a special form of the modulus.
 */

.section .text

/**
 * Unrolled 768=384x384 bit multiplication.
 *
 * Returns c = a x b.
 *
 * Flags: Last instruction performs a dummy addition on the highest limb of c.
 * Therefore the routine is left with the flags being set based on this
 * operation:
 *    - M: MSb of the result (and the highest limb of the result)
 *    - L: LSb of the highest limb of result
 *    - Z: Indicates if highest limb of result is zero
 *    - C: Never set
 *
 * @param[in] [w9, w8]: a, first operand, max. length 384 bit.
 * @param[in] [w11, w10]: b, second operand, max. length 384 bit.
 * @param[in] w31: all-zero.
 * @param[out] [w18, w17, w16]: c, result, max. length 768 bit.
 *
 * Clobbered flag groups: FG0
 */
mul384:
  bn.mulqacc.z          w8.0, w10.0,   0
  bn.mulqacc            w8.0, w10.1,  64
  bn.mulqacc.so w16.L,  w8.1, w10.0,  64
  bn.mulqacc            w8.0, w10.2,   0
  bn.mulqacc            w8.1, w10.1,   0
  bn.mulqacc            w8.2, w10.0,   0
  bn.mulqacc            w8.0, w10.3,  64
  bn.mulqacc            w8.1, w10.2,  64
  bn.mulqacc            w8.2, w10.1,  64
  bn.mulqacc.so w16.U,  w8.3, w10.0,  64
  bn.mulqacc            w8.0, w11.0,   0
  bn.mulqacc            w8.1, w10.3,   0
  bn.mulqacc            w8.2, w10.2,   0
  bn.mulqacc            w8.3, w10.1,   0
  bn.mulqacc            w9.0, w10.0,   0
  bn.mulqacc            w8.0, w11.1,  64
  bn.mulqacc            w8.1, w11.0,  64
  bn.mulqacc            w8.2, w10.3,  64
  bn.mulqacc            w8.3, w10.2,  64
  bn.mulqacc            w9.0, w10.1,  64
  bn.mulqacc.so w17.L,  w9.1, w10.0,  64
  bn.mulqacc            w8.1, w11.1,   0
  bn.mulqacc            w8.2, w11.0,   0
  bn.mulqacc            w8.3, w10.3,   0
  bn.mulqacc            w9.0, w10.2,   0
  bn.mulqacc            w9.1, w10.1,   0
  bn.mulqacc            w8.2, w11.1,  64
  bn.mulqacc            w8.3, w11.0,  64
  bn.mulqacc            w9.0, w10.3,  64
  bn.mulqacc.so w17.U,  w9.1, w10.2,  64
  bn.mulqacc            w8.3, w11.1,   0
  bn.mulqacc            w9.0, w11.0,   0
  bn.mulqacc            w9.1, w10.3,   0
  bn.mulqacc            w9.0, w11.1,  64
  bn.mulqacc.so w18.L,  w9.1, w11.0,  64
  bn.mulqacc.so w18.U,  w9.1, w11.1,   0

  bn.add w18, w18, w31

  ret

/**
 * 384-bit modular multiplication based on Barrett reduction algorithm.
 *
 * Returns c = a x b % m.
 *
 * Expects: two operands, modulus and pre-calculated parameter u for barrett
 * reduction (usually greek mu in literature). u is expected without the
 * leading 1 at bit 384. u has to be pre-calculated as u = floor(2^768/m).
 * This guarantees that u > 2^384. However, in order for u to be at
 * most 2^385-1, it has to be ensured that m >= 2^383 + 1.
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
 * @param[in] [w9, w8]: a, first operand, max. length 384 bit, a < m.
 * @param[in] [w11, w10]: b, second operand, max. length 384 bit, b < m.
 * @param[in] [w13, w12]: m, modulus, max. length 384 bit, 2^384 > m > 2^383.
 * @param[in] [w15, w14]: u, pre-computed Barrett constant (without u[384]/MSb
 *                           of u which is always 1 for the allowed range but
 *                           has to be set to 0 here).
 * @param[in] w31: all-zero.
 * @param[out] [w30, w29]: c, result, max. length 384 bit.
 *
 * Clobbered registers: w16, w17, w18, w19, w20, w21, w22, w23, w24
 * Clobbered flag groups: FG0
 */
barrett384:
  /* Compute the integer product of the operands x = a * b
     x = [w18, w17, w16] = a * b = [w9, w8] * [w11, w10]
     => max. length x: 768 bit */
  jal x1, mul384

  /* Store correction factor to compensate for later neglected MSb of x.
     x is 768 bit wide and therefore the 383 bit right shifted version q1
     (below) contains 385 bit. Bit 384 of q1 is neglected to allow using a
     384x384 multiplier. For the MSb of x being set we temporary store u
     (or zero) here to be used in a later constant time correction of a
     multiplication with u. Note that this requires the MSb flag being carried
     over from the multiplication routine. */
  bn.sel w24, w14, w31, M
  bn.sel w25, w15, w31, M

  /* save lower limbs of x. [w22, w21] = x[511:0] = [w17,w16] */
  bn.mov w21, w16
  bn.mov w22, w17

  /* Compute q1 = x >> 383
     q1 = [w9, w8] = [w18, w17, w16] >> 383  = [w18, w17] >> 127
     => max length q1: 385 bits */
  bn.rshi w9, w31, w18 >> 127
  bn.rshi w8, w18, w17 >> 127

  /* Compute q2 = q1*u
     Instead of full q2 (which would be up to 770 bits) we ignore the MSb of u
     and the MSb of q1 and correct this later. This allows using a 384x384
     multiplier. For special modili where the lower half of the second limb of
     u is zero (e.g. p384) this can be further optimized by only considering
     limb 0 of u and use a 384x256 multiplication.
     => max. length q2': 768 bit
     q2' = q1[383:0]*u[383:0] = [w18, w17, w16] = [w9, w8] * [w15, w14] */
  bn.mov w10, w14
  bn.mov w11, w15
  jal x1, mul384

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
     q2''' = q2'' + q1 = [w20, w19] = [w20, w19] + [w8, w9] */
  bn.add w19, w19, w8
  bn.addc w20, w20, w9
  /* Conditionally add u (without leading 1) in case of MSb of x being set.
     This is the "real" q2 but shifted by 384 bits to the right. This cannot
     overflow due to leading zeros
     q2'''' = x[767]?q2'''+u[383:0]:q2'''
            = [w20, w19] + [w25, w24] = q2 >> 384 */
  bn.add w19, w19, w24
  bn.addc w20, w20, w25
  /* finally this gives q3 by shifting the remaining bit to the right
     q3 = q2 >> 385 = q2'''' >> 1 = [w9, w8] = [w20, w19] >> 1 */
  bn.rshi w9, w31, w20 >> 1
  bn.rshi w8, w20, w19 >> 1

  /* Compute r = q3 * m
     => max. length r: 768 bit
     r2 = q3*m = [w18, w17, w16] = [w9, w8] * [w13, w12]
     A 384x384 bit multiplication kernel is used here, hence both q3 and m
     must not be wider than 384 bit. This is always the case for m. For q3 it
     is the case if a<m and b<m. */
  bn.mov w10, w12
  bn.mov w11, w13
  jal x1, mul384

  /* Compute r = x-r2 = x-q3*m
     since 0 <= r < 3*m, we only need to consider the lower limbs of x and r2
     r[511:0] = [w22, w21] - [w17, w16] */
  bn.sub w21, w21, w16
  bn.subb w22, w22, w17

  /* Barrett algorithm requires subtraction of the modulus at most two times if
     result is too large. */
  bn.sub w29, w21, w12
  bn.subb w30, w22, w13
  bn.sel w21, w21, w29, C
  bn.sel w22, w22, w30, C
  bn.sub w29, w21, w12
  bn.subb w30, w22, w13
  bn.sel w29, w21, w29, C
  bn.sel w30, w22, w30, C

  /* return result: c =[w29, w30] =  a * b % m. */
  ret


/**
 * Externally callable wrapper for modular multiplication with
 * Barrett reduction.
 *
 * Returns c = a x b % m.
 *
 * @param[in]  dmem[47:0]: a, first operand, max. length 384 bit
 * @param[in]  dmem[111:64]: b, second operand, max. length 384 bit
 * @param[in]  dmem[303:256]: m, modulus, max. length 384 bit
 *                            with 2^384 > m > 2^383
 * @param[in]  dmem[367:320]: u, pre-computed Barrett constant
 *                               (without u[384]/MSb of u which is always 1
 *                               for the allowed range but has to be set to 0
 *                               here).
 * @param[out] dmem[559:512]: c, result, max. length 384 bit.
 */
.globl wrap_barrett384
wrap_barrett384:
  bn.xor w31, w31, w31

  /* load first operand from dmem to [w9, w8] */
  li x4, 8
  bn.lid x4++, 0(x0)
  bn.lid x4++, 32(x0)
  /* load second operand from dmem to [w11, w10] */
  bn.lid x4++, 64(x0)
  bn.lid x4++, 96(x0)
  /* load modulus from dmem to [w13, w12] */
  bn.lid x4++, 256(x0)
  bn.lid x4++, 288(x0)
  /* load barrett precomputed parameter u from dmem to [w15, w14] */
  bn.lid x4++, 320(x0)
  bn.lid x4++, 352(x0)

  jal x1, barrett384

  /* store result from [w30, w29] to dmem */
  li x4, 29
  bn.sid x4++, 512(x0)
  bn.sid x4++, 544(x0)

  ecall
