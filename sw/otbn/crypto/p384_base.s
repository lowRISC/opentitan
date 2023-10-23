/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   This library contains:
 *   - P-384 specific routines for point addition in projective space
 *   - P-384 domain parameters
 *   - P-384 specific routines for multiplication and reduction of large values
 */

 .section .text

/**
 * Unrolled 768=384x384 bit multiplication.
 *
 * Returns c = a x b.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w11, w10]: a, first operand, max. length 384 bit, b < m.
 * @param[in] [w17, w16]: b, second operand, max. length 384 bit, b < m.
 * @param[in] w31: all-zero.
 * @param[out] [w20:w18]: c, result, max. length 768 bit.
 *
 * Clobbered registers: w18 to w20
 * Clobbered flag groups: FG0
 */
mul384:
  bn.mulqacc.z          w10.0, w16.0,   0
  bn.mulqacc            w10.0, w16.1,  64
  bn.mulqacc.so w18.L,  w10.1, w16.0,  64
  bn.mulqacc            w10.0, w16.2,   0
  bn.mulqacc            w10.1, w16.1,   0
  bn.mulqacc            w10.2, w16.0,   0
  bn.mulqacc            w10.0, w16.3,  64
  bn.mulqacc            w10.1, w16.2,  64
  bn.mulqacc            w10.2, w16.1,  64
  bn.mulqacc.so w18.U,  w10.3, w16.0,  64
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
  bn.mulqacc.so w19.L,  w11.1, w16.0,  64
  bn.mulqacc            w10.1, w17.1,   0
  bn.mulqacc            w10.2, w17.0,   0
  bn.mulqacc            w10.3, w16.3,   0
  bn.mulqacc            w11.0, w16.2,   0
  bn.mulqacc            w11.1, w16.1,   0
  bn.mulqacc            w10.2, w17.1,  64
  bn.mulqacc            w10.3, w17.0,  64
  bn.mulqacc            w11.0, w16.3,  64
  bn.mulqacc.so w19.U,  w11.1, w16.2,  64
  bn.mulqacc            w10.3, w17.1,   0
  bn.mulqacc            w11.0, w17.0,   0
  bn.mulqacc            w11.1, w16.3,   0
  bn.mulqacc            w11.0, w17.1,  64
  bn.mulqacc.so w20.L,  w11.1, w17.0,  64
  bn.mulqacc.so w20.U,  w11.1, w17.1,   0

  ret

/**
 * Unrolled 572=448x128 bit multiplication.
 *
 * Returns c = a x b.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w11, w10]: a, first operand, max. length 448 bit, a < m.
 * @param[in] w16: b, second operand, max. length 128 bit, b < m.
 * @param[in] w31: all-zero.
 * @param[out] [w20:w18]: c, result, max. length 572 bit.
 *
 * Clobbered registers: w18 to w20
 * Clobbered flag groups: FG0
 */
mul448x128:
  bn.mulqacc.z          w10.0, w16.0, 0
  bn.mulqacc            w10.0, w16.1, 64
  bn.mulqacc.so  w18.L, w10.1, w16.0, 64
  bn.mulqacc            w10.1, w16.1, 0
  bn.mulqacc            w10.2, w16.0, 0
  bn.mulqacc            w10.2, w16.1, 64
  bn.mulqacc.so  w18.U, w10.3, w16.0, 64
  bn.mulqacc            w10.3, w16.1, 0
  bn.mulqacc            w11.0, w16.0, 0
  bn.mulqacc            w11.1, w16.0, 64
  bn.mulqacc.so  w19.L, w11.0, w16.1, 64
  bn.mulqacc            w11.2, w16.0, 0
  bn.mulqacc            w11.1, w16.1, 0
  bn.mulqacc.so  w19.U, w11.2, w16.1, 64
  bn.mulqacc.wo    w20, w31.0, w31.0, 0

  ret

/**
 * Solinas reduction algorithm.
 *
 * Returns c = a mod m = (x + 2^384 * y) mod m.
 *
 * This subroutine is specialized to the coordinate field of P-384 and cannot
 * be used for other moduli.
 *
 * Solinas reduction is based on the observation that if the modulus has the
 * form (2^384 - K), then for all x and y:
 *   (x + 2^384 * y) mod (2^384 - K) = (x + K * y) mod (2^384 - K).
 *
 * For P-384, the constant K is: (2^128 + 2^96 - 2^32 + 1). A "Solinas
 * reduction step" consists of splitting a large number (such as the result of
 * a multiplication) into two parts: the lowest 384 bits (x in the formula
 * above) and any bits above that point (y in the formula above), then
 * multiplying y by K and adding it to x. Because of K's special form, the
 * multiplication by K for the P-384 modulus is especially quick.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w20:w18]: a, input to reduce, max. length 768 bit.
 * @param[in] [w13, w12]: m, modulus, 2^383 <= m < 2^384.
 * @param[in] w31: all-zero.
 * @param[out] [w17, w16]: c, result, max. length 384 bit.
 *
 * Clobbered registers: w16 to w24
 * Clobbered flag groups: FG0
 */
.globl p384_reduce_p
p384_reduce_p:
  /* Solinas reduction step. Based on the observation that:
     (x + 2^384 * y) mod (2^384 - K) = (x + K * y) mod (2^384 - K).

    For P-384, the constant K = 2^384 - modulus is: (2^128 + 2^96 - 2^32 + 1)
   */

  /* Extract the high 128 bits from the middle term and the low 128 bits from
     the high term:
       w21 <= ab[639:384] */
  bn.rshi w21, w20, w19 >> 128

  /* Multiply by K:
     [w24:w23] <= w21 + (w21 << 128) + (w21 << 96) - (w21 << 32) = ab[639:384] * K */
  bn.add  w23, w21, w21 << 128
  bn.addc w24, w31, w21 >> 128
  bn.add  w23, w23, w21 << 96
  bn.addc w24, w24, w21 >> 160
  bn.sub  w23, w23, w21 << 32
  bn.subb w24, w24, w21 >> 224

  /* Construct a 256-bit mask:
       w22 <= 2^256 - 1 */
  bn.not  w22, w31

  /* Isolate the lower 384 bits:
       w19 <= ab[383:256] */
  bn.and  w19, w19, w22 >> 128

  /* Add product to the lower 384 bits:
       [w19:w18] = ab[383:0] + (ab[639:384] * K) */
  bn.add  w18, w18, w23
  bn.addc w19, w19, w24

  /* Isolate the highest 128 bits of the product:
       [w24:w23] <= ab[767:640] */
  bn.rshi w21, w31, w20 >> 128

  /* Multiply by K:
     [w24:w23] <= w21 + (w21 << 128) + (w21 << 96) - (w21 << 32) = ab[767:640] * K */
  bn.add  w23, w21, w21 << 128
  bn.addc w24, w31, w21 >> 128
  bn.add  w23, w23, w21 << 96
  bn.addc w24, w24, w21 >> 160
  bn.sub  w23, w23, w21 << 32
  bn.subb w24, w24, w21 >> 224

  /* Add product to the result to complete the reduction step:
       [w20:w18] = ab[383:0] + (ab[767:384] * K) */
  bn.add  w19, w19, w23
  bn.addc w20, w31, w24

  /* At this point, the intermediate result r is max. 576 bits, because:
       ab[383:0]: 384 bits
       ab[767:384]: 384 bits
       ab[767:384] * K : 575 bits
       r = ab[383:0] + ab[767:384] * K : 576 bits

    Start another Solinas step to reduce the bound further. */

  /* Extract the high 192 bits:
       w21 <= r[575:384] * K */
  bn.rshi w21, w20, w19 >> 128

  /* Multiply by K:
     [w24:w23] <= w21 + (w21 << 128) + (w21 << 96) - (w21 << 32) = r[575:384] * K */
  bn.add  w23, w21, w21 << 128
  bn.addc w24, w31, w21 >> 128
  bn.add  w23, w23, w21 << 96
  bn.addc w24, w24, w21 >> 160
  bn.sub  w23, w23, w21 << 32
  bn.subb w24, w24, w21 >> 224

  /* Isolate the lower 384 bits:
       w19 <= r[383:256] */
  bn.and  w19, w19, w22 >> 128

  /* Add product to the lower 384 bits to complete the reduction step:
       [w19:w18] = r[383:0] + (r[575:384] * K) */
  bn.add  w18, w18, w23
  bn.addc w19, w19, w24

  /* At this point, the result is at most 385 bits, and a conditional
     subtraction is sufficient to fully reduce. */
  bn.sub  w16, w18, w12
  bn.subb w17, w19, w13

  /* If the subtraction underflowed (C is set), select the pre-subtraction
     result; otherwise, select the result of the subtraction. */
  bn.sel w16, w18, w16, C
  bn.sel w17, w19, w17, C

  ret

/**
 * Solinas reduction algorithm.
 *
 * Returns c = a mod m = (x + 2^384 * y) mod m.
 *
 * This subroutine is intended for use with the group order (n) of P-384, but
 * will work for any modulus m such that 2^384 - 2^191 < m < 2^384.
 *
 * Solinas reduction is based on the observation that if the modulus has the
 * form (2^384 - K), then for all x and y:
 *   (x + 2^384 * y) mod (2^384 - K) = (x + K * y) mod (2^384 - K).
 *
 * A "Solinas reduction step" consists of splitting a large number (such as the
 * result of a multiplication) into two parts: the lowest 384 bits (x in the
 * formula above) and any bits above that point (y in the formula above), then
 * multiplying y by K and adding it to x.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w20:w18]: a, input to reduce, max. length 768 bit.
 * @param[in] [w13, w12]: m, modulus, 2^383 <= m < 2^384.
 * @param[in] w14: k, Solinas constant (2^384 - modulus), max. length 191 bit.
 * @param[in] w31: all-zero.
 * @param[out] [w17, w16]: c, result, max. length 384 bit.
 *
 * Clobbered registers: w16 to w24
 * Clobbered flag groups: FG0
 */
.globl p384_reduce_n
p384_reduce_n:
  /* Extract the high 128 bits from the middle term and the low 128 bits from
     the high term:
       w21 <= ab[639:384] */
  bn.rshi w21, w20, w19 >> 128

  /* Multiply by K (256bx192b multiplication):
       [w24:w23] <= w21 * w14 = ab[639:384] * K */
  bn.mulqacc.z          w21.0, w14.0,   0
  bn.mulqacc            w21.0, w14.1,  64
  bn.mulqacc.so w23.L,  w21.1, w14.0,  64
  bn.mulqacc            w21.0, w14.2,   0
  bn.mulqacc            w21.1, w14.1,   0
  bn.mulqacc            w21.2, w14.0,   0
  bn.mulqacc            w21.1, w14.2,  64
  bn.mulqacc            w21.2, w14.1,  64
  bn.mulqacc.so w23.U,  w21.3, w14.0,  64
  bn.mulqacc            w21.2, w14.2,   0
  bn.mulqacc            w21.3, w14.1,   0
  bn.mulqacc.wo w24,    w21.3, w14.2,  64

  /* Construct a 256-bit mask:
       w22 <= 2^256 - 1 */
  bn.not  w22, w31

  /* Isolate the lower 384 bits:
       w19 <= ab[383:256] */
  bn.and  w19, w19, w22 >> 128

  /* Add product to the lower 384 bits:
       [w19:w18] = ab[383:0] + (ab[639:384] * K) */
  bn.add  w18, w18, w23
  bn.addc w19, w19, w24

  /* Isolate the highest 128 bits of the product:
       [w24:w23] <= ab[767:640] */
  bn.rshi w21, w31, w20 >> 128

  /* Multiply by K (128bx192b multiplication):
     [w24:w23] <=  ab[767:640] * K */
  bn.mulqacc.z          w21.0, w14.0,   0
  bn.mulqacc            w21.0, w14.1,  64
  bn.mulqacc.so w23.L,  w21.1, w14.0,  64
  bn.mulqacc            w21.0, w14.2,   0
  bn.mulqacc            w21.1, w14.1,   0
  bn.mulqacc.so w23.U,  w21.1, w14.2,  64
  /* Write remaining accumulator to w24; multiply by known zeroes to avoid
     changing the accumulator. */
  bn.mulqacc.wo w24,    w31.0, w31.0,   0

  /* Add product to the result to complete the reduction step:
       [w20:w18] = ab[383:0] + (ab[767:384] * K) */
  bn.add  w19, w19, w23
  bn.addc w20, w31, w24

  /* At this point, the intermediate result r is max. 576 bits, because:
       ab[383:0]: 384 bits
       ab[767:384]: 384 bits
       ab[767:384] * K : 575 bits
       r = ab[383:0] + ab[767:384] * K : 576 bits

    Start another Solinas step to reduce the bound further. */

  /* Extract the high 192 bits:
       w21 <= r[575:384] * K */
  bn.rshi w21, w20, w19 >> 128

  /* Multiply by K (192bx192b multiplication):
       [w24:w23] <= w21 * w14 = r[575:384] * K */
  bn.mulqacc.z          w21.0, w14.0,   0
  bn.mulqacc            w21.0, w14.1,  64
  bn.mulqacc.so w23.L,  w21.1, w14.0,  64
  bn.mulqacc            w21.0, w14.2,   0
  bn.mulqacc            w21.1, w14.1,   0
  bn.mulqacc            w21.2, w14.0,   0
  bn.mulqacc            w21.1, w14.2,  64
  bn.mulqacc.so w23.U,  w21.2, w14.1,  64
  bn.mulqacc.wo w24,    w21.2, w14.2,   0

  /* Isolate the lower 384 bits:
       w19 <= r[383:256] */
  bn.and  w19, w19, w22 >> 128

  /* Add product to the lower 384 bits to complete the reduction step:
       [w19:w18] = r[383:0] + (r[575:384] * K) */
  bn.add  w18, w18, w23
  bn.addc w19, w19, w24

  /* At this point, the result is at most 385 bits, and a conditional
     subtraction is sufficient to fully reduce. */
  bn.sub  w16, w18, w12
  bn.subb w17, w19, w13

  /* If the subtraction underflowed (C is set), select the pre-subtraction
     result; otherwise, select the result of the subtraction. */
  bn.sel w16, w18, w16, C
  bn.sel w17, w19, w17, C

  ret

/**
 * 384-bit modular multiplication based on Solinas reduction algorithm.
 *
 * Returns c = a x b % p.
 *
 * This subroutine is specialized to the coordinate field of P-384 and cannot
 * be used for other moduli.
 *
 * For mor information on the reduction algorith, see 'p384_reduce_p'.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w11, w10]: a, first operand, max. length 384 bit, b < m.
 * @param[in] [w17, w16]: b, second operand, max. length 384 bit, b < m.
 * @param[in] [w13, w12]: m, modulus, 2^383 <= m < 2^384.
 * @param[in] w31: all-zero.
 * @param[out] [w17, w16]: c, result, max. length 384 bit.
 *
 * Clobbered registers: w16 to w24
 * Clobbered flag groups: FG0
 */
.globl p384_mulmod_p
p384_mulmod_p:
  /* Compute the raw 768-bit product:
       ab = [w20:w18] <= a * b */
  jal     x1, mul384

  /* return [w17, w16] = ab mod m = [w20:w18] mod m */
  jal     x0, p384_reduce_p

/**
 * 384-bit modular multiplication based on Solinas reduction algorithm.
 *
 * Returns c = a * b mod m.
 *
 * This subroutine is intended for use with the group order (n) of P-384, but
 * will work for any modulus m such that 2^384 - 2^191 < m < 2^384.
 *
 * For mor information on the reduction algorith, see 'p384_reduce_n'.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w11, w10]: a, first operand, max. length 384 bit, b < m.
 * @param[in] [w17, w16]: b, second operand, max. length 384 bit, b < m.
 * @param[in] [w13, w12]: m, modulus, 2^383 <= m < 2^384.
 * @param[in] w14: k, Solinas constant (2^384 - modulus), max. length 191 bit.
 * @param[in] w31: all-zero.
 * @param[out] [w17, w16]: c, result, max. length 384 bit.
 *
 * Clobbered registers: w16 to w24
 * Clobbered flag groups: FG0
 */
.globl p384_mulmod_n
p384_mulmod_n:
  /* Compute the raw 768-bit product:
       ab = [w20:w18] <= a * b */
  jal     x1, mul384

  /* return [w17, w16] = ab mod m = [w20:w18] mod m */
  jal     x0, p384_reduce_n

/**
 * 448x128=572-bit modular multiplication based on Solinas reduction algorithm.
 *
 * Returns c = a * b mod m.
 *
 * This subroutine is intended for use with the group order (n) of P-384, but
 * will work for any modulus m such that 2^384 - 2^191 < m < 2^384.
 *
 * For mor information on the reduction algorith, see 'p384_reduce_n'.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w11, w10]: a, first operand, max. length 384 bit, b < m.
 * @param[in] w16: b, second operand, max. length 128 bit, b < m.
 * @param[in] [w13, w12]: m, modulus, 2^383 <= m < 2^384.
 * @param[in] w14: k, Solinas constant (2^384 - modulus), max. length 191 bit.
 * @param[in] w31: all-zero.
 * @param[out] [w17, w16]: c, result, max. length 384 bit.
 *
 * Clobbered registers: w16 to w24
 * Clobbered flag groups: FG0
 */
.globl p384_mulmod448x128_n
p384_mulmod448x128_n:
  /* Compute the raw 768-bit product:
       ab = [w20:w18] <= a * b */
  jal     x1, mul448x128

  /* return [w17, w16] = ab mod m = [w20:w18] mod m */
  jal     x0, p384_reduce_n

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
 * @param[in]  x22: set to 10, pointer to in reg for modular multiplication
 * @param[in]  x23: set to 11, pointer to in reg for modular multiplication
 * @param[in]  x24: set to 16, pointer to in/out reg for modular multiplication
 * @param[in]  x25: set to 17, pointer to in/out reg for modular multiplication
 * @param[in]  x26: dptr_p_p, dmem pointer to point P in dmem (projective)
 * @param[in]  x27: dptr_q_p, dmem pointer to point Q in dmem (projective)
 * @param[in]  x28: dptr_b, dmem pointer to domain parameter b of P-384 in dmem
 * @param[in]  [w13, w12]: p, modulus of underlying field of P-384
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
  jal       x1, p384_mulmod_p
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* 2: [w3, w2] = t1 <= Y1*Y2 = dmem[x26+64]*dmem[x27+64] */
  bn.lid    x22, 64(x26)
  bn.lid    x23, 96(x26)
  bn.lid    x24, 64(x27)
  bn.lid    x25, 96(x27)
  jal       x1, p384_mulmod_p
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 3: [w5, w4] = t2 <= Z1*Z2 = dmem[x26+128]*dmem[x27+128] */
  bn.lid    x22, 128(x26)
  bn.lid    x23, 160(x26)
  bn.lid    x24, 128(x27)
  bn.lid    x25, 160(x27)
  jal       x1, p384_mulmod_p
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
  bn.sel    w6, w16, w10, C
  bn.sel    w7, w17, w11, C

  /* 5: [w9, w8] = t4 <= X2+Y2 = dmem[x27+0]+dmem[x27+64] */
  bn.lid    x22, 0(x27)
  bn.lid    x23, 32(x27)
  bn.lid    x24, 64(x27)
  bn.lid    x25, 96(x27)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w8, w16, w10, C
  bn.sel    w9, w17, w11, C

  /* 6: [w7, w6] = t3 <= t3*t4 = [w7, w6]*[w9, w8] */
  bn.mov    w10, w6
  bn.mov    w11, w7
  bn.mov    w16, w8
  bn.mov    w17, w9
  jal       x1, p384_mulmod_p
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* 7: [w9, w8] = t4 <= t0+t1 = [w1, w0]+[w3, w2] */
  bn.add    w16, w0, w2
  bn.addc   w17, w1, w3
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w8, w16, w10, C
  bn.sel    w9, w17, w11, C

  /* 8: [w7, w6] = t3 <= t3-t4 = [w7, w6]-[w9, w8] */
  bn.sub    w16, w6, w8
  bn.subb   w17, w7, w9
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w6, w10, w16, C
  bn.sel    w7, w11, w17, C

  /* 9: [w9, w8] = t4 <= Y1+Z1 = dmem[x26+64]+dmem[x26+128] */
  bn.lid    x22, 64(x26)
  bn.lid    x23, 96(x26)
  bn.lid    x24, 128(x26)
  bn.lid    x25, 160(x26)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w8, w16, w10, C
  bn.sel    w9, w17, w11, C

  /* 10: [w26, w25] = X3 <= Y2+Z2 = dmem[x27+64]+dmem[x27+128] */
  bn.lid    x22, 64(x27)
  bn.lid    x23, 96(x27)
  bn.lid    x24, 128(x27)
  bn.lid    x25, 160(x27)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w25, w16, w10, C
  bn.sel    w26, w17, w11, C

  /* 11: [w9, w8] = t4 <= t4*X3 = [w9, w8]*[w26, w25] */
  bn.mov    w10, w8
  bn.mov    w11, w9
  bn.mov    w16, w25
  bn.mov    w17, w26
  jal       x1, p384_mulmod_p
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* 12: [w26, w25] = X3 <= t1+t2 = [w3, w2]+[w5, w4] */
  bn.add    w16, w2, w4
  bn.addc   w17, w3, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w25, w16, w10, C
  bn.sel    w26, w17, w11, C

  /* 13: [w9, w8] = t4 <= t4-X3 = [w9, w8]-[w26, w25] */
  bn.sub    w16, w8, w25
  bn.subb   w17, w9, w26
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w8, w10, w16, C
  bn.sel    w9, w11, w17, C

  /* 14: [w26, w25] = X3 <= X1+Z1 = dmem[x26+0]+dmem[x26+128] */
  bn.lid    x22, 0(x26)
  bn.lid    x23, 32(x26)
  bn.lid    x24, 128(x26)
  bn.lid    x25, 160(x26)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w25, w16, w10, C
  bn.sel    w26, w17, w11, C

  /* 15: [w28, w27] = Y3 <= X2+Z2 = dmem[x27+0]+dmem[x27+128] */
  bn.lid    x22, 0(x27)
  bn.lid    x23, 32(x27)
  bn.lid    x24, 128(x27)
  bn.lid    x25, 160(x27)
  bn.add    w16, w10, w16
  bn.addc   w17, w11, w17
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w27, w16, w10, C
  bn.sel    w28, w17, w11, C

  /* 16: [w26, w25] = X3 <= X3*Y3 = [w26, w25]*[w28, w27] */
  bn.mov    w10, w25
  bn.mov    w11, w26
  bn.mov    w16, w27
  bn.mov    w17, w28
  jal       x1, p384_mulmod_p
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 17: [w28, w27] = Y3 <= t0+t2 = [w1, w0]+[w5, w4] */
  bn.add    w16, w0, w4
  bn.addc   w17, w1, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w27, w16, w10, C
  bn.sel    w28, w17, w11, C

  /* 18: [w28, w27] = Y3 <= X3-Y3 = [w26, w25]-[w28, w27] */
  bn.sub    w16, w25, w27
  bn.subb   w17, w26, w28
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w27, w10, w16, C
  bn.sel    w28, w11, w17, C

  /* 19: [w30, w29] = Z3 <= b*t2 = dmem[x28+0]*[w5, w4] */
  bn.lid    x22, 0(x28)
  bn.lid    x23, 32(x28)
  bn.mov    w16, w4
  bn.mov    w17, w5
  jal       x1, p384_mulmod_p
  bn.mov    w29, w16
  bn.mov    w30, w17

  /* 20: [w26, w25] = X3 <= Y3-Z3 = [w28, w27]-[w30, w29] */
  bn.sub    w16, w27, w29
  bn.subb   w17, w28, w30
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w25, w10, w16, C
  bn.sel    w26, w11, w17, C

  /* 21: [w30, w29] = Z3 <= X3+X3 = [w26, w25]+[w26, w25] */
  bn.add    w16, w25, w25
  bn.addc   w17, w26, w26
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w29, w16, w10, C
  bn.sel    w30, w17, w11, C

  /* 22: [w26, w25] = X3 <= X3+Z3 = [w26, w25]+[w30, w29] */
  bn.add    w16, w25, w29
  bn.addc   w17, w26, w30
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w25, w16, w10, C
  bn.sel    w26, w17, w11, C

  /* 23: [w30, w29] = Z3 <= t1-X3 = [w3, w2]-[w26, w25] */
  bn.sub    w16, w2, w25
  bn.subb   w17, w3, w26
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w29, w10, w16, C
  bn.sel    w30, w11, w17, C

  /* 24: [w26, w25] = X3 <= t1+X3 = [w3, w2]+[w26, w25] */
  bn.add    w16, w2, w25
  bn.addc   w17, w3, w26
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w25, w16, w10, C
  bn.sel    w26, w17, w11, C

  /* 25: [w28, w27] = Y3 <= b*Y3 = dmem[x28+0]*[w28, w27] */
  bn.lid    x22, 0(x28)
  bn.lid    x23, 32(x28)
  bn.mov    w16, w27
  bn.mov    w17, w28
  jal       x1, p384_mulmod_p
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 26: [w3, w2] = t1 <= t2+t2 = [w5, w4]+[w5, w4] */
  bn.add    w16, w4, w4
  bn.addc   w17, w5, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w2, w16, w10, C
  bn.sel    w3, w17, w11, C

  /* 27: [w5, w4] = t2 <= t1+t2 = [w3, w2]+[w5, w4] */
  bn.add    w16, w2, w4
  bn.addc   w17, w3, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w4, w16, w10, C
  bn.sel    w5, w17, w11, C

  /* 28: [w28, w27] = Y3 <= Y3-t2 = [w28, w27]-[w5, w4] */
  bn.sub    w16, w27, w4
  bn.subb   w17, w28, w5
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w27, w10, w16, C
  bn.sel    w28, w11, w17, C

  /* 29: [w28, w27] = Y3 <= Y3-t0 = [w28, w27]-[w1, w0] */
  bn.sub    w16, w27, w0
  bn.subb   w17, w28, w1
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w27, w10, w16, C
  bn.sel    w28, w11, w17, C

  /* 30: [w3, w2] = t1 <= Y3+Y3 = [w28, w27]+[w28, w27] */
  bn.add    w16, w27, w27
  bn.addc   w17, w28, w28
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w2, w16, w10, C
  bn.sel    w3, w17, w11, C

  /* 31: [w28, w27] = Y3 <= t1+Y3 = [w3, w2]+[w28, w27] */
  bn.add    w16, w2, w27
  bn.addc   w17, w3, w28
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w27, w16, w10, C
  bn.sel    w28, w17, w11, C

  /* 32: [w3, w2] = t1 <= t0+t0 = [w1, w0]+[w1, w0] */
  bn.add    w16, w0, w0
  bn.addc   w17, w1, w1
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w2, w16, w10, C
  bn.sel    w3, w17, w11, C

  /* 33: [w1, w0] = t0 <= t1+t0 = [w3, w2]+[w1, w0] */
  bn.add    w16, w2, w0
  bn.addc   w17, w3, w1
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w0, w16, w10, C
  bn.sel    w1, w17, w11, C

  /* 34: [w1, w0] = t0 <= t0-t2 = [w1, w0]-[w5, w4] */
  bn.sub    w16, w0, w4
  bn.subb   w17, w1, w5
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w0, w10, w16, C
  bn.sel    w1, w11, w17, C

  /* 35: [w3, w2] = t1 <= t4*Y3 = [w9, w8]*[w28, w27] */
  bn.mov    w10, w8
  bn.mov    w11, w9
  bn.mov    w16, w27
  bn.mov    w17, w28
  jal       x1, p384_mulmod_p
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 36: [w5, w4] = t2 <= t0*Y3 = [w1, w0]*[w28, w27] */
  bn.mov    w10, w0
  bn.mov    w11, w1
  bn.mov    w16, w27
  bn.mov    w17, w28
  jal       x1, p384_mulmod_p
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* 37: [w28, w27] = Y3 <= X3*Z3 = [w26, w25]*[w30, w29] */
  bn.mov    w10, w25
  bn.mov    w11, w26
  bn.mov    w16, w29
  bn.mov    w17, w30
  jal       x1, p384_mulmod_p
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* 38: [w28, w27] = Y3 <= Y3+t2 = [w28, w27]+[w5, w4] */
  bn.add    w16, w27, w4
  bn.addc   w17, w28, w5
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w27, w16, w10, C
  bn.sel    w28, w17, w11, C

  /* 39: [w26, w25] = X3 <= t3*X3 = [w7, w6]*[w26, w25] */
  bn.mov    w10, w6
  bn.mov    w11, w7
  bn.mov    w16, w25
  bn.mov    w17, w26
  jal       x1, p384_mulmod_p
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* 40: [w26, w25] = X3 <= X3-t1 = [w26, w25]-[w3, w2] */
  bn.sub    w16, w25, w2
  bn.subb   w17, w26, w3
  bn.add    w10, w16, w12
  bn.addc   w11, w17, w13
  bn.sel    w25, w10, w16, C
  bn.sel    w26, w11, w17, C

  /* 41: [w30, w29] = Z3 <= t4*Z3 = [w9, w8]*[w30, w29] */
  bn.mov    w10, w8
  bn.mov    w11, w9
  bn.mov    w16, w29
  bn.mov    w17, w30
  jal       x1, p384_mulmod_p
  bn.mov    w29, w16
  bn.mov    w30, w17

  /* 42: [w3, w2] = t1 <= t3*t0 = [w7, w6]*[w1, w0] */
  bn.mov    w10, w6
  bn.mov    w11, w7
  bn.mov    w16, w0
  bn.mov    w17, w1
  jal       x1, p384_mulmod_p
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* 43: [w30, w29] = Z3 <= Z3+t1 = [w30, w29]+[w3, w2] */
  bn.add    w16, w29, w2
  bn.addc   w17, w30, w3
  bn.sub    w10, w16, w12
  bn.subb   w11, w17, w13
  bn.sel    w29, w16, w10, C
  bn.sel    w30, w17, w11, C

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
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w26,w25]: x, x-coordinate of curve point (projective).
 * @param[in]  [w28,w27]: y, y-coordinate of curve point (projective).
 * @param[in]  [w30,w29]: z, z-coordinate of curve point (projective).
 * @param[in]  [w13, w12]: p, modulus of P-384.
 * @param[in]  w31: all-zero.
 * @param[out] [w1, w0]: z^-1. inverse of z-coordinate of curve point.
 * @param[out] [w26, w25]: x_a, affine x-coordinate of resulting point.
 * @param[out] [w28, w27]: y_a, affine y-coordinate of resulting point.
 *
 * clobbered registers: w0 to w28
 * clobbered flag groups: FG0
 */
 .globl proj_to_affine_p384
proj_to_affine_p384:

  /* Exp: 0b10 = 2*0b1
     Val: r10 = z^2 mod p
          [w17,w16] <= [w30,w29]^2 mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  bn.mov    w16, w29
  bn.mov    w17, w30
  jal       x1, p384_mulmod_p

  /* Exp: 0b11 = 0b1+0b10
     Val: r11 <= z*r10 mod p
          [w17,w16] <= [w30,w29]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p

  /* Exp: 0b110 = 2*0b11
     Val: r110 = r11^2 mod p
          [w17,w16] <= [w17,w16]^2 mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, p384_mulmod_p

  /* Exp: 0b111 = 0b1+0b110
     Val: r111 <= z*r110  mod p
          [w1,w0] = [w17,w16] <= [w30,w29]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* Exp: 0b111000 = 0b111<<3
     Val: r111000 <= r111^(2^3)  mod p
          [w17,w16] <= [w17,w16]^(2^3) mod [w13,w12] */
  loopi     3, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop

  /* Exp: 0b1111111 = 0b111+0b111000
     Val: r1111111 <= r111*r111000 mod p
          [w3,w2] = [w17,w16] <= [w1,w0]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, p384_mulmod_p
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* Exp: 2^12-1 = (0b1111111<<6)+0b111111
     Val: r_12_1 <= r111111^(2^6)*r111111 mod p
          [w5,w4] = [w17,w16] <= [w17,w16]^(2^6)*[w17,w16] mod [w13,w12] */
  loopi     6, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, p384_mulmod_p
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* Exp: 2^24-1 = ((2^12-1)<<12)+(2^12-1)
     Val: r_24_1 <= r_12_1^(2^12)*r12_1 mod p
          [w17,w16] <= [w17,w16]^(2^12)*[w5,w4] mod [w13,w12] */
  loopi     12, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w4
  bn.mov    w11, w5
  jal       x1, p384_mulmod_p

  /* Exp: 2^30-1 = ((2^24-1)<<6)+0b111111
     Val: r_30_1 <= r_24_1^(2^6)*r111111 mod p
          [w3, w2] = [w17,w16] <= [w17,w16]^(2^6)*[w3,w2] mod [w13,w12] */
  loopi     6, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, p384_mulmod_p
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* Exp: 2^31-1 <= (2^30-1)*2+0b1
     Val: r_31_1 <= r30_1^2*z mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^2*[w30,w29] mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, p384_mulmod_p
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* Exp: 2^32-1 <= (2^30-1)*2+0b1
     Val: r_32_1 <= r31_1^2*z mod p
          [w9,w8] = [w17,w16] <= [w17,w16]^2*[w30,w29] mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, p384_mulmod_p
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p
  bn.mov    w9, w16
  bn.mov    w8, w17

  /* Exp: 2^63-1 <= ((2^32-1)<<31)+(2^31-1)
     Val: r_63_1 <= r_32_1^(2^31)*r_31_1 mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^(2^31)*[w7,w6] mod [w13,w12] */
  loopi     31, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, p384_mulmod_p
  bn.mov    w6, w16
  bn.mov    w7,w17

  /* Exp: 2^126-1 = ((2^63-1)<<63) + (2^63-1)
     Val: r_126_1 <= r_63_1^(2^63)*r_63_1 mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^(2^63)*[w7,w6] mod [w13,w12] */
  loopi     63, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, p384_mulmod_p
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* Exp: 2^252-1 = ((2^126-1)<<126)+(2^126-1)
     Val: r_252_1 <= r_126_1^(2^63)*r_126_1 mod p
          [w17,w16] <= [w17,w16]^(2^126)*[w7,w6] mod [w13,w12] */
  loopi     126, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, p384_mulmod_p

  /* Exp: 2^255-1 = ((2^252-1)<<3)+0b111
     Val: r_255_1 <= r_252_1^(2^3)*r111 mod p
          [w17,w16] <= [w17,w16]^(2^3)*[w1,w0] mod [w13,w12] */
  loopi     3, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, p384_mulmod_p

  /* Exp: p-2 = ((((((2^255-1)<<33)+(2^32-1))<<94)+(2^30-1))<<2)+0b1
     Val: x_inv <=((r_255_1^(2^33)*r_32_1)^(2^94)*r_30_1)^(2^2)*z mod p
          [w17,w16] <= (([w17,w16]^(2^33)*[w9,w8])^(2^94)*[w3,w2])^(2^2)
                       *[w30,w29] mod [w13,w12] */
  loopi     33, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w9
  bn.mov    w11, w8
  jal       x1, p384_mulmod_p
  loopi     94, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, p384_mulmod_p
  loopi     2, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p

  /* store inverse [w1,w0] <= [w17,w16] = z_inv*/
  bn.mov w0, w16
  bn.mov w1, w17

  /* convert x-coordinate to affine space
     [w26,w25] <= [w17,w16] = x_a <= x/z = x*z_inv = [w26,w25]*[w1,w0] mod p */
  bn.mov    w10, w25
  bn.mov    w11, w26
  jal       x1, p384_mulmod_p
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* convert y-coordinate to affine space
     [w28,w27] <= [w17,w16] = y_a <= y/z = y*z_inv = [w28,w27]*[w1,w0] mod p */
  bn.mov    w10, w27
  bn.mov    w11, w28
  bn.mov    w16, w0
  bn.mov    w17, w1
  jal       x1, p384_mulmod_p
  bn.mov    w27, w16
  bn.mov    w28, w17

  ret

.section .data

.balign 32

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
