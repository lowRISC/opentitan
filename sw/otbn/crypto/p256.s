/* Copyright lowRISC Contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_p256.c
 */

.globl p256_isoncurve
.globl p256_scalar_mult
.globl p256_base_mult
.globl p256_sign
.globl p256_verify
.globl proj_add

.text

/**
 * 256-bit modular multiplication based on Barrett reduction algorithm.
 *
 * Returns c = a * b mod p
 *
 * Expects two 256 bit operands, 256 bit modulus and pre-computed parameter u
 * for Barrett reduction (usually greek mu in literature). u is expected
 * without the leading 1 at bit 256. u has to be pre-computed as
 * u = floor(2^512/p).
 * This guarantees that u > 2^256, however, in order for u to be at
 * most 2^257-1, it has to be ensured that p >= 2^255 + 1.
 *
 * This implementation mostly follows the description in the
 * "Handbook of Applied Cryptography" in Algorithm 14.42.
 * Differences:
 *   - This implementation incorporates a multiplication before the reduction.
 *     Therefore it expects two operands (a, b) instead of a wider integer x.
 *   - The computation of q2 ignores the MSbs of q1 and u to allow using
 *     a 256x256 bit multiplication. This is compensated later by
 *     individual (conditional) additions.
 *   - The truncations in step 2 of HAC 14.42 in the form of (... mod b^(k+1) )
 *     are not implemented here and the full register width is used. This
 *     allows to omit computation of r1 (since r1=x) and step 3 of HAC 14.42
 *   - There is only a single conditional subtraction of the modulus at the end
 *
 * Note that this implementation is targeted and tested to be used with modulus
 * and Barrett constant of the P-256 underlying finite field only. For a
 * generic modulus a 2nd conditional subtraction of the modulus has to be
 * added or the modulus has to be in a range such that it can be mathematically
 * proven that a single subtraction is sufficient.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w24: a, first 256 bit operand (a * b < 2^256 * p)
 * @param[in]  w25: b, second 256 bit operand (a * b < 2^256 * p)
 * @param[in]  w29: p, modulus of P-256 underlying finite field
 * @param[in]  w28: u, lower 256 bit of Barrett constant for curve P-256
 * @param[in]  w31: all-zero
 * @param[in]  MOD: p, modulus of P-256 underlying finite field
 * @param[out]  w19: c, result
 *
 * clobbered registers: w19, w20, w21, w22, w23, w24, w25
 * clobbered flag groups: FG0
 */
mod_mul_256x256:
  /* Compute the integer product of the operands x = a * b
     x = [w20, w19] = a * b = w24 * w25
     => max. length x: 512 bit */
  bn.mulqacc.z          w24.0, w25.0,  0
  bn.mulqacc            w24.1, w25.0, 64
  bn.mulqacc.so  w19.L, w24.0, w25.1, 64
  bn.mulqacc            w24.2, w25.0,  0
  bn.mulqacc            w24.1, w25.1,  0
  bn.mulqacc            w24.0, w25.2,  0
  bn.mulqacc            w24.3, w25.0, 64
  bn.mulqacc            w24.2, w25.1, 64
  bn.mulqacc            w24.1, w25.2, 64
  bn.mulqacc.so  w19.U, w24.0, w25.3, 64
  bn.mulqacc            w24.3, w25.1,  0
  bn.mulqacc            w24.2, w25.2,  0
  bn.mulqacc            w24.1, w25.3,  0
  bn.mulqacc            w24.3, w25.2, 64
  bn.mulqacc.so  w20.L, w24.2, w25.3, 64
  bn.mulqacc.so  w20.U, w24.3, w25.3,  0
  bn.add    w20, w20, w31

  /* Store correction factor to compensate for later neglected MSb of x.
     x is 512 bit wide and therefore the 255 bit right shifted version q1
     (below) contains 257 bit. Bit 256 of q1 is neglected to allow using a
     256x256 multiplier. For the MSb of x being set we temporary store u
     (or zero) here to be used in a later constant time correction of a
     multiplication with u. Note that this requires the MSb flag being carried
     over from the multiplication routine. */
  bn.sel    w22, w28, w31, M

  /* Compute q1' = q1[255:0] = x >> 255
     w21 = q1' = [w20, w19] >> 255 */
  bn.rshi   w21, w20, w19 >> 255

  /* Compute q2 = q1*u
     Instead of full q2 (which would be up to 514 bits) we ignore the MSb of u
     and the MSb of q1 and correct this later. This allows using a 256x256
     multiplier.
     => max. length q2': 512 bit
     q2' = q1[255:0]*u[255:0] = [w20, w19] = w21 * w28 */
  bn.mulqacc.z          w21.0, w28.0,  0
  bn.mulqacc            w21.1, w28.0, 64
  bn.mulqacc.so  w23.L, w21.0, w28.1, 64
  bn.mulqacc            w21.2, w28.0,  0
  bn.mulqacc            w21.1, w28.1,  0
  bn.mulqacc            w21.0, w28.2,  0
  bn.mulqacc            w21.3, w28.0, 64
  bn.mulqacc            w21.2, w28.1, 64
  bn.mulqacc            w21.1, w28.2, 64
  bn.mulqacc.so  w23.U, w21.0, w28.3, 64
  bn.mulqacc            w21.3, w28.1,  0
  bn.mulqacc            w21.2, w28.2,  0
  bn.mulqacc            w21.1, w28.3,  0
  bn.mulqacc            w21.3, w28.2, 64
  bn.mulqacc.so  w24.L, w21.2, w28.3, 64
  bn.mulqacc.so  w24.U, w21.3, w28.3,  0
  bn.add    w20, w20, w31

  /* q3 = q2 >> 257
     In this step, the compensation for the neglected MSbs of q1 and u is
     carried out underway. To add them in the q2 domain, they would have to be
     left shifted by 256 bit first. To directly add them we first shift q2' by
     256 bit to the right (by dropping the lower 256 bit), perform the
     additions, and shift the result another bit to the right.

  /* w25 = q1[256] = x[511:256] >> 255 */
  bn.rshi   w25, w31, w20 >> 255

  /* compensate for neglected MSB of u, by adding full q1
     this is unconditional since MSB of u is always 1
     [w25, w24] = q2'' <= q2'[511:256] + q1 = [w25, w24] <= w24 + [w25, w21] */
  bn.add    w24, w24, w21
  bn.addc   w25, w25, w31

  /* compensate for neglected MSB of q1, by conditionally adding u */
  /* [w25, w24] = q2''' <= q2'' + [0 or u] = [w25, w24] + w22 */
  bn.add    w24, w24, w22
  bn.addc   w25, w25, w31

  /* q3 = w21 = q2''' >> 1 */
  bn.rshi   w21, w25, w24 >> 1

  /* [w23, w22] <= q3 * p  */
  bn.mulqacc.z          w29.0, w21.0,  0
  bn.mulqacc            w29.1, w21.0, 64
  bn.mulqacc.so  w22.L, w29.0, w21.1, 64
  bn.mulqacc            w29.2, w21.0,  0
  bn.mulqacc            w29.1, w21.1,  0
  bn.mulqacc            w29.0, w21.2,  0
  bn.mulqacc            w29.3, w21.0, 64
  bn.mulqacc            w29.2, w21.1, 64
  bn.mulqacc            w29.1, w21.2, 64
  bn.mulqacc.so  w22.U, w29.0, w21.3, 64
  bn.mulqacc            w29.3, w21.1,  0
  bn.mulqacc            w29.2, w21.2,  0
  bn.mulqacc            w29.1, w21.3,  0
  bn.mulqacc            w29.3, w21.2, 64
  bn.mulqacc.so  w23.L, w29.2, w21.3, 64
  bn.mulqacc.so  w23.U, w29.3, w21.3,  0
  bn.add    w23, w23, w31

  /* We compute the final remainder r by subtracting the estimate q3 from x.
     In the generic algorithm, r is already the reduced result or it is off by
     either p or 2p. For the special case of the modulus of P-256 it can be
     shown that r can only be off by max p. Therefore, only a single
     conditional correction is required.
     [w20, w22] = r <= [w20, w19] - [w23, w22] = x - q3*p  */
  bn.sub    w22, w19, w22
  bn.subb   w20, w20, w23

  /* r cannot be wider than 257 bit. Therefore it is r > p if bit 256 of r is
     set and we need to subtract the modulus */
  bn.sel    w21, w29, w31, L
  bn.sub    w21, w22, w21

  /* this performs the correction in case r is only 256 bit long but still
     greater than the modulus */
  bn.addm   w19, w21, w31

  ret


/**
 * Checks if a point is a valid curve point on curve P-256 (secp256r1)
 *
 * Returns r = x^3 + ax + b  mod p
 *     and s = y^2  mod p
 *         with x,y being the affine coordinates of the curve point
 *              a, b and p being the domain parameters of P-256
 *
 * This routine checks if a point with given x- and y-coordinate is a valid
 * curve point on P-256.
 * The routine checks whether the coordinates are a solution of the
 * Weierstrass equation y^2 = x^3 + ax + b  mod p.
 * The routine makes use of the property that the domain parameter 'a' can be
 * written as a=-3 for the P-256 curve, hence the routine is limited to P-256.
 * The routine does not return a boolean result but computes the left side
 * and the right sight of the Weierstrass equation and leaves the final
 * comparison to the caller.
 * The routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[x]: affine x-coordinate of input point
 * @param[in]  dmem[y]: affine y-coordinate of input point
 * @param[out] dmem[r]: right side result r
 * @param[out] dmem[s]: left side result s
 *
 * clobbered registers: x2, x3, x19, x20, w0, w19 to w25
 * clobbered flag groups: FG0
 */
p256_isoncurve:

  /* setup all-zero reg */
  bn.xor    w31, w31, w31

  /* setup modulus p and Barrett constant u
     MOD <= w29 <= dmem[p256_p] = p; w28 <= dmem[p256_u_p] = u_p */
  li        x2, 29
  la        x3, p256_p
  bn.lid    x2, 0(x3)
  bn.wsrw   0, w29
  li        x2, 28
  la        x3, p256_u_p
  bn.lid    x2, 0(x3)

  /* load domain parameter b from dmem
     w27 <= b = dmem[p256_b] */
  li        x2, 27
  la        x3, p256_b
  bn.lid    x2, 0(x3)

  /* load affine y-coordinate of curve point from dmem
     w26 <= dmem[y] */
  la        x3, y
  li        x2, 24
  bn.lid    x2, 0(x3)

  /* w19 <= y^2 = w24*w24 */
  bn.mov    w25, w24
  jal       x1, mod_mul_256x256

  /* store left side result: dmem[s] <= w19 = y^2  mod p */
  la        x20, s
  li        x2, 19
  bn.sid    x2, 0(x20)

  /* load affine x-coordinate of curve point from dmem
     w26 <= dmem[x] */
  la        x3, x
  li        x2, 26
  bn.lid    x2, 0(x3)

  /* w19 <= x^2 = w26*w26 */
  bn.mov    w25, w26
  bn.mov    w24, w26
  jal       x1, mod_mul_256x256

  /* w19 = x^3 <= x^2 * x = w25*w24 = w26*w19 */
  bn.mov    w25, w19
  bn.mov    w24, w26
  jal       x1, mod_mul_256x256

  /* for curve P-256, 'a' can be written as a = -3, therefore we subtract
     x three times from x^3.
     w19 = x^3 + ax <= x^3 - 3x  mod p */
  bn.subm   w19, w19, w26
  bn.subm   w19, w19, w26
  bn.subm   w19, w19, w26

  /* w24 <= x^3 + ax + b mod p = w19 + w27 mod p */
  bn.addm   w19, w19, w27

  /* store right side result: dmem[r] <= w19 = x^3 + ax + b mod p */
  la        x19, r
  li        x2, 19
  bn.sid    x2, 0(x19)

  ret


/**
 * P-256 point addition in projective coordinates
 *
 * returns R = (x_r, y_r, z_r) <= P+Q = (x_p, y_p, z_p) + (x_q, y_q, z_q)
 *         with R, P and Q being valid P-256 curve points
 *           in projective coordinates
 *
 * This routine adds two valid P-256 curve points in projective space.
 * Point addition is performed based on the complete formulas of Bosma and
 * Lenstra for Weierstrass curves as first published in [1] and
 * optimized in [2].
 * The implemented version follows Algorithm 4 of [2] which is an optimized
 * variant for Weierstrass curves with domain parameter 'a' set to a=-3.
 * Numbering of the steps below and naming of symbols follows the
 * terminology of Algorithm 4 of [2].
 * The routine is limited to P-256 curve points due to:
 *   - fixed a=-3 domain parameter
 *   - usage of a P-256 optimized Barrett multiplication kernel
 * This routine runs in constant time.
 *
 * [1] https://doi.org/10.1006/jnth.1995.1088
 * [2] https://doi.org/10.1007/978-3-662-49890-3_16
 *
 * @param[in]  w8: x_p, x-coordinate of input point P
 * @param[in]  w9: y_p, y-coordinate of input point P
 * @param[in]  w10: z_p, z-coordinate of input point P
 * @param[in]  w11: x_q, x-coordinate of input point Q
 * @param[in]  w12: y_q, x-coordinate of input point Q
 * @param[in]  w13: z_q, x-coordinate of input point Q
 * @param[in]  w27: b, curve domain parameter
 * @param[in]  w29: p, modulus, 2^256 > p > 2^255.
 * @param[in]  w28: u, pre-computed Barrett constant (without u[256]/MSb
 *                           of u which is always 1 for the allowed range.
 * @param[in]  w31: all-zero.
 * @param[in]  MOD: p, modulus, 2^256 > p > 2^255.
 * @param[out]  w11: x_r, x-coordinate of resulting point R
 * @param[out]  w12: y_r, x-coordinate of resulting point R
 * @param[out]  w13: z_r, x-coordinate of resulting point R
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: w11 to w25
 * clobbered flag groups: FG0
 */
proj_add:
  /* mapping of parameters to symbols of [2] (Algorithm 4):
     X1 = x_p; Y1 = y_p; Z1 = z_p; X2 = x_q; Y2 = y_q; Z2 = z_q
     X3 = x_r; Y3 = y_r; Z3 = z_r */

  /* 1: w14 = t0 <= X1*X2 = w11*w8 */
  bn.mov    w24, w11
  bn.mov    w25, w8
  jal       x1, mod_mul_256x256
  bn.mov    w14, w19

  /* 2: w15 = t1 <= Y1*Y2 = w12*w9 */
  bn.mov    w24, w12
  bn.mov    w25, w9
  jal       x1, mod_mul_256x256
  bn.mov    w15, w19

  /* 3: w16 = t2 <= Z1*Z2 = w13*w10*/
  bn.mov    w24, w13
  bn.mov    w25, w10
  jal       x1, mod_mul_256x256
  bn.mov    w16, w19

  /* 5: w17 = t4 <= X2+Y2 = w11 + w12 */
  bn.addm   w17, w11, w12

  /* 4: w18 = t3 <= X1+Y1 = w8+w9 */
  bn.addm   w18, w8, w9

  /* 6: w19 = t3 <= t3*t4 = w18*w17 */
  bn.mov    w24, w17
  bn.mov    w25, w18
  jal       x1, mod_mul_256x256

  /* 7: w18 = t4 <= t0+t1 = w14+w15 */
  bn.addm   w18, w14, w15

  /* 8: w17 = t3 <= t3 - t4 = w19 - w18 */
  bn.subm   w17, w19, w18

  /* 10: w18 = X3 <= Y2 + Z2 = w12 + w13 */
  bn.addm   w18, w12, w13

  /* 9: w19 = t4 <= Y1 + Z1 = w9 + w10 */
  bn.addm   w19, w9, w10

  /* 11: w18 = t4 <= t4 * X3 = w19 * w18 */
  bn.mov    w24, w18
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256
  bn.mov    w18, w19

  /* 12: w19 = X3 <= t1 + t2 = w15 + w16 */
  bn.addm   w19, w15, w16

  /* 13: w18 = t4 <= t4 - X3 = w18 + w19 */
  bn.subm   w18, w18, w19

  /* 15: w19 = Y3 <= X2 + Z2 = w11 + w13 */
  bn.addm   w19, w11, w13

  /* 14: w12 = X3 <= X1 + Z1 = w8 + w10 */
  bn.addm   w12, w8, w10

  /* 16: w11 = X3 <= X3 * Y3 = w12 * w19 */
  bn.mov    w24, w19
  bn.mov    w25, w12
  jal       x1, mod_mul_256x256
  bn.mov    w11, w19

  /* 17: w12 = Y3 <= t0 + t2 = w14 + w16 */
  bn.addm   w12, w14, w16

  /* 18: w12 = Y3 <= X3 - Y3 = w11 - w12 */
  bn.subm   w12, w11, w12

  /* 19: w19 = Z3 <= b * t2 =  w27 * w16 */
  bn.mov    w24, w27
  bn.mov    w25, w16
  jal       x1, mod_mul_256x256

  /* 20: w11 = X3 <= Y3 -Z3 = w12 - w19 */
  bn.subm   w11, w12, w19

  /* 21: w13 = Z3 <= X3 + X3 = w11 + w11 */
  bn.addm   w13, w11, w11

  /* 22: w11 = X3 <= w11 + w13 = X3 + Z3 */
  bn.addm   w11, w11, w13

  /* 23: w13 = Z3 <= t1 - X3 = w15 - w11 */
  bn.subm   w13, w15, w11

  /* 24: w11 = X3 <= t1 + X3 = w15 + w11 */
  bn.addm   w11, w15, w11

  /* 25: w19 = Y3 <= w27 * w12 = b * Y3 */
  bn.mov    w24, w27
  bn.mov    w25, w12
  jal       x1, mod_mul_256x256

  /* 26: w15 = t1 <= t2 + t2 = w16 + w16 */
  bn.addm   w15, w16, w16

  /* 27: w16 = t2 <= t1 + t2 = w15 + w16 */
  bn.addm   w16, w15, w16

  /* 28: w12 = Y3 <= Y3 - t2 = w19 - w16 */
  bn.subm   w12, w19, w16

  /* 29: w12 = Y3 <= Y3 - t0 = w12 - w14 */
  bn.subm   w12, w12, w14

  /* 30: w15 = t1 <= Y3 + Y3 = w12 + w12 */
  bn.addm   w15, w12, w12

  /* 31: w12 = Y3 <= t1 + Y3 = w15 + w12*/
  bn.addm   w12, w15, w12

  /* 32: w15 = t1 <= t0 + t0 = w14 + w14 */
  bn.addm   w15, w14, w14

  /* 33: w14 = t0 <= t1 + t0 = w15 + w14 */
  bn.addm   w14, w15, w14

  /* 34: w14 = t0 <= t0 - t2 = w14 - w16 */
  bn.subm   w14, w14, w16

  /* 35: w15 = t1 <= t4 * Y3 = w18 * w12 */
  bn.mov    w24, w18
  bn.mov    w25, w12
  jal       x1, mod_mul_256x256
  bn.mov    w15, w19

  /* 36: w16 = t2 <= t0 * Y3 = w14 * w12 */
  bn.mov    w24, w14
  bn.mov    w25, w12
  jal       x1, mod_mul_256x256
  bn.mov    w16, w19

  /* 37: w12 = Y3 <= X3 * Z3 = w11 * w13 */
  bn.mov    w24, w11
  bn.mov    w25, w13
  jal       x1, mod_mul_256x256

  /* 38: w12 = Y3 <= Y3 + t2 = w19 + w16 */
  bn.addm   w12, w19, w16

  /* 39: w19 = X3 <= t3 * X3 = w17 * w11 */
  bn.mov    w24, w17
  bn.mov    w25, w11
  jal       x1, mod_mul_256x256

  /* 40: w11 = X3 <= X3 - t1 = w19 - w15 */
  bn.subm   w11, w19, w15

  /* 41: w13 = Z3 <= t4 * Z3 = w18 * w13 */
  bn.mov    w24, w18
  bn.mov    w25, w13
  jal       x1, mod_mul_256x256
  bn.mov    w13, w19

  /* 42: w19 = t1 <= t3 * t0 = w17 * w14 */
  bn.mov    w24, w17
  bn.mov    w25, w14
  jal       x1, mod_mul_256x256

  /* 43: w13 = Z3 <= Z3 + t1 = w13 + w19 */
  bn.addm   w13, w13, w19

  ret


/**
 * Convert projective coordinates of a P-256 curve point to affine coordinates
 *
 * returns P = (x_a, y_a) = (x/z mod p, y/z mod p)
 *         with P being a valid P-256 curve point
 *              x_a and y_a being the affine coordinates of said curve point
 *              x, y and z being a set of projective coordinates of said point
 *              and p being the modulus of the P-256 underlying finite field.
 *
 * This routine computes the affine coordinates for a set of projective
 * coordinates of a valid P-256 curve point. The routine performs the required
 * divisions by computing the multiplicative modular inverse of the
 * projective z-coordinate in the underlying finite field of the P-256 curve.
 * For inverse computation Fermat's little theorem is used, i.e.
 * we compute z^-1 = z^(p-2) mod p.
 * For exponentiation a 27 step addition chain is used.
 * This addition chain is (presumably?) the shortest addition chain known as
 * of today for the exponent exp = p - 2 = 2^256 -  2^224 + 2^6 + 2^64 - 1 - 2.
 * Origin of the chain can not fully be traced. [1] attributes it to a specific
 * patch to OpenSLL. The same addition chain is used in the OpenSSL and
 * BoringSSL crypto libraries.
 * This routine runs in constant time.
 *
 * [1] https://doi.org/10.1007/s13389-014-0090-x
 *     https://eprint.iacr.org/2013/816.pdf
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * @param[in]  w8: x, x-coordinate of curve point (projective)
 * @param[in]  w9: y, y-coordinate of curve point (projective)
 * @param[in]  w10: z, z-coordinate of curve point (projective)
 * @param[in]  w29: p, modulus, 2^256 > p > 2^255.
 * @param[in]  w28: u, pre-computed Barrett constant (without u[256]/MSb
 *                           of u which is always 1 for the allowed range.
 * @param[in]  MOD: p, modulus of the finite field of P-256
 * @param[out]  w11: x_a, x-coordinate of curve point (affine)
 * @param[out]  w12: y_a, y-coordinate of curve point (affine)
 *
 * clobbered registers: w10 to w19, w24, w25
 * clobbered flag groups: FG0
 */
proj_to_affine:

  /* 1: exp = 0x1 */
  bn.addm   w10, w10, w31

  /* 2: exp = 0x2 = 2*0x1 */
  bn.mov    w24, w10
  bn.mov    w25, w10
  jal       x1, mod_mul_256x256

  /* 3: exp = 0x3 = 0x2+0x1 */
  bn.mov    w24, w19
  bn.mov    w25, w10
  jal       x1, mod_mul_256x256
  bn.mov    w12, w19

  /* 4: exp = 0x6 = 2*0x3 */
  bn.mov    w24, w19
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* 5: exp = 0xc = 2*0x6 */
  bn.mov    w24, w19
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* 6: exp = 0xf = 0xc+0x3 */
  bn.mov    w24, w19
  bn.mov    w25, w12
  jal       x1, mod_mul_256x256
  bn.mov    w13, w19

  /* 7: exp = 0xf0 = 16*0xf */
  loopi     4, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop

  /* 8: exp = 0xff = 0xf0+0xf */
  bn.mov    w24, w19
  bn.mov    w25, w13
  jal       x1, mod_mul_256x256
  bn.mov    w14, w19

  /* 9: exp = 0xff00 = 256*0xff */
  loopi     8, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop

  /* 10: exp = 0xffff = 0xff00+0xff */
  bn.mov    w24, w19
  bn.mov    w25, w14
  jal       x1, mod_mul_256x256
  bn.mov    w15, w19

  /* 11: exp = 0xffff0000 = 2^16*0xffff */
  loopi     16, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop

  /* 12: exp = 0xffffffff = 0xffff0000+0xffff */
  bn.mov    w24, w19
  bn.mov    w25, w15
  jal       x1, mod_mul_256x256
  bn.mov    w16, w19

  /* 13: exp = 0xffffffff00000000 = 2^32*0xffffffff */
  loopi     32, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop
  bn.mov    w17, w19

  /* 14: exp = 0xffffffff00000001 = 0xffffffff00000000+0x1 */
  bn.mov    w24, w10
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* 15: exp =
           0xffffffff00000001000000000000000000000000000000000000000000000000
         = 2^192*0xffffffff00000001 */
  loopi     192, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop
  bn.mov    w18, w19

  /* 16: exp = 0xffffffffffffffff = 0xffffffff00000000+0xffffffff */
  bn.mov    w24, w17
  bn.mov    w25, w16
  jal       x1, mod_mul_256x256

  /* 17: exp = 0xffffffffffffffff0000 = 2^16*0xffffffffffffffff */
  loopi     16, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop

  /* 18: exp = 0xffffffffffffffffffff = 0xffffffffffffffff0000+0xffff */
  bn.mov    w24, w15
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* 19: exp = 0xffffffffffffffffffff00 = 256*0xffffffffffffffffffff */
  loopi     8, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop

  /* 20: exp = 0xffffffffffffffffffffff = 0xffffffffffffffffffff00+0xff */
  bn.mov    w24, w14
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* 21: exp = 0xffffffffffffffffffffff0 = 16*0xffffffffffffffffffffff */
  loopi     4, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop

  /* 22: exp = 0xfffffffffffffffffffffff = 0xffffffffffffffffffffff0+0xf */
  bn.mov    w24, w13
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* 23: exp = 0x3ffffffffffffffffffffffc = 4*0xfffffffffffffffffffffff */
  loopi     2, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop

  /* 24: exp = 0x3fffffffffffffffffffffff = 0x3ffffffffffffffffffffffc+0x3 */
  bn.mov    w24, w12
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* 25: exp = 0xfffffffffffffffffffffffc = 4*0x3fffffffffffffffffffffff */
  loopi     2, 4
    bn.mov    w24, w19
    bn.mov    w25, w19
    jal       x1, mod_mul_256x256
    nop

  /* 26: exp = 0xfffffffffffffffffffffffd = 0xfffffffffffffffffffffffc+0x1 */
  bn.mov    w24, w10
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* 27: exp = p-2
         = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd
         = 0xfffffffffffffffffffffffd
         + 0xffffffff00000001000000000000000000000000000000000000000000000000
     w14 = z^exp = z^(p-2) = z^-1   mod p */
  bn.mov    w24, w19
  bn.mov    w25, w18
  jal       x1, mod_mul_256x256
  bn.mov    w14, w19

  /* convert x-coordinate to affine
     w11 = x_a = x/z = x * z^(-1) = w8 * w14 */
  bn.mov    w24, w8
  bn.mov    w25, w14
  jal       x1, mod_mul_256x256
  bn.mov    w11, w19

  /* convert y-coordinate to affine
     w12 = y_a = y/z = y * z^(-1) = w9 * w14 */
  bn.mov    w24, w9
  bn.mov    w25, w14
  jal       x1, mod_mul_256x256
  bn.mov    w12, w19

  ret


/**
 * Variable time modular multiplicative inverse computation
 *
 * returns x_inv = x^-1 mod m
 *
 * This routine computes the modular multiplicative inverse for any x < m in
 * the field GF(m).
 * For inverse computation Fermat's little theorem is used, i.e.
 * we compute x^-1 = x^(m-2) mod m.
 * For exponentiation we use a standard, variable time (!) square and multiply
 * algorithm.
 *
 * @param[in]  w0: x, a 256 bit operand with x < m
 * @param[in]  w29: m, modulus, 2^256 > m > 2^255.
 * @param[in]  w28: u, lower 256 bit of pre-computed Barrett constant
 * @param[in]  w31, all-zero
 * @param[in]  MOD: m, modulus
 * @param[out]  w1: x_inv, modular multiplicative inverse
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: w1, w2, w3, w19, w24, w25
 * clobbered flag groups: FG0
 */
mod_inv:

  /* subtract 2 from modulus for Fermat's little theorem
     w2 = MOD - 2 = m - 2 */
  bn.wsrr   w2, 0
  bn.subi   w2, w2, 2

  /* init square and multiply: w1 = 1 */
  bn.addi   w1, w31, 1

  /* square and multiply loop */
  loopi     256, 14

    /* square: w3 = w19 = w24*w25 = w1^2  mod m */
    bn.mov    w24, w1
    bn.mov    w25, w1
    jal       x1, mod_mul_256x256
    bn.mov    w3, w19

    /* shift MSB into carry flag
       w2 = 2*w2 = w2 << 1 */
    bn.add    w2, w2, w2

    /* skip multiplication if C flag not set */
    bn.sel    w1, w1, w3, C
    csrrs     x2, 0x7c0, x0
    andi      x2, x2, 1
    beq       x2, x0, nomul

    /* multiply: w1 = w19 = w24*w25 = w3*w0  mod m */
    bn.mov    w24, w3
    bn.mov    w25, w0
    jal       x1, mod_mul_256x256
    bn.mov    w1, w19

    nomul:
    nop

  ret


/**
 * Fetch curve point from dmem and randomize z-coordinate
 *
 * returns P = (x, y, z) = (x_a*z, y_a*z, z)
 *         with P being a valid P-256 curve point in projective coordinates
 *              x_a and y_a being the affine coordinates as fetched from dmem
 *              z being a randomized z-coordinate
 *
 * This routines fetches the affine x- and y-coordinates of a curve point from
 * dmem and computes a valid set of projective coordinates. The z-coordinate is
 * randomized and x and y are scaled appropriately.
 * This routine runs in constant time.
 *
 * @param[in]  x10: constant 24
 * @param[in]  x21: dptr_x, pointer to dmem location containing affine
 *                          x-coordinate of input point
 * @param[in]  x22: dptr_y, pointer to dmem location containing affine
 *                          y-coordinate of input point
 * @param[in]  w28: u, lower 256 bit of Barrett constant for curve P-256
 * @param[in]  w29: p, modulus of P-256 underlying finite field
 * @param[in]  w31: all-zero
 * @param[in]  MOD: p, modulus of P-256 underlying finite field
 * @param[out]  w26: z, random projective z-coordinate
 * @param[out]  w6: x, projective x-coordinate
 * @param[out]  w7: y, projective y-coordinate
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the scaled projective y-coordinate.
 *
 * clobbered registers: w2, w6, w7, w19 to w26
 * clobbered flag groups: FG0
 */
fetch_proj_randomize:

  /* get random number from URND */
  bn.wsrr   w2, 2

  /* reduce random number
     w26 = z <= w2 mod p */
  bn.addm   w26, w2, w31

  /* fetch x-coordinate from dmem
     w24 = x_a <= dmem[x22] = dmem[dptr_x] */
  bn.lid    x10, 0(x21)

  /* scale x-coordinate
     w6 = x <= w24*w26 = x_a*z  mod p */
  bn.mov    w25, w26
  jal       x1, mod_mul_256x256
  bn.mov    w6, w19

  /* fetch y-coordinate from dmem
     w24 = y_a <= dmem[x22] = dmem[dptr_y] */
  bn.lid    x10, 0(x22)

  /* scale y-coordinate
     w7 = y <= w24*w26 = y_a*z  mod p */
  bn.mov    w25, w26
  jal       x1, mod_mul_256x256
  bn.mov    w7, w19

  ret


/**
 * P-256 point doubling in projective space
 *
 * returns R = (x_r, y_r, z_r) <= 2*P = 2*(x_p, y_p, z_p)
 *         with R, P being valid P-256 curve points
 *
 * This routines doubles a given P-256 curve point in projective coordinate.
 * Internally this routine makes use of the point addition routine and
 * adds the point to itself.
 * This routine runs in constant time.
 *
 * @param[in]  w8: x_p, x-coordinate of input point
 * @param[in]  w9: y_p, y-coordinate of input point
 * @param[in]  w10: z_p, z-coordinate of input point
 * @param[in]  w27: b, curve domain parameter
 * @param[in]  w29: p, p, modulus of P-256 underlying finite field
 * @param[in]  w28: u, u, lower 256 bit of Barrett constant for curve P-256
 * @param[in]  w31: all-zero.
 * @param[in]  MOD: p, modulus of P-256 underlying finite field
 * @param[out]  w11: x_r, x-coordinate of resulting point
 * @param[out]  w12: y_r, y-coordinate of resulting point
 * @param[out]  w13: z_r, z-coordinate of resulting point
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: w11 to w25
 * clobbered flag groups: FG0
 */
proj_double:

  /* Q = (x_q, y_q, z_q) = (w11, w12, w13) <= P = (x_p, y_p, z_p)
     = (w8, w9, w10) */
  bn.mov    w11, w8
  bn.mov    w12, w9
  bn.mov    w13, w10

  /* R = (x_r, y_r, z_r) = (w11, w12, w13) = P+Q
       = (w8, w9, w10) + (w11, w12, w13) = (x_p, y_p, z_p) + (x_q, y_q, z_q) */
  jal       x1, proj_add

  ret


/**
 * P-256 scalar point multiplication in affine space
 *
 * returns R = k*P = k*(x_p, y_p)
 *         with R, P being valid P-256 curve points in affine coordinates
 *              k being a 256 bit scalar
 *
 * This routine performs scalar multiplication based on the group laws
 * of Weierstrass curves.
 * A constant time double-and-add algorithm (sometimes referred to as
 * double-and-add-always) is used.
 * Due to the P-256 optimized implementations of the called routines for
 * point addition and doubling, this routine is limited to P-256.
 * The routine makes use of blinding by additive splitting the
 * exponent/scalar k into a random number (rnd) and rnd-k. The double-and-add
 * loop operates on both shares in parallel applying Shamir's trick.
 *
 * @param[in]  x21: dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]  x22: dptr_y, pointer to affine y-coordinate in dmem
 * @param[in]  w0: k, scalar for multiplication
 * @param[in]  w1: rnd, blinding parameter
 * @param[in]  w27: b, curve domain parameter
 * @param[in]  w31: all-zero
 * @param[in]  MOD: p, modulus, 2^256 > p > 2^255.
 * @param[out]  w11: x_r, affine x-coordinate of resulting point
 * @param[out]  w12: y_r, affine y-coordinate of resulting point
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x10, w0 to w26
 * clobbered flag groups: FG0
 */
scalar_mult_int:

  /* load order of base point G of P-256
     w29 <= n = dmem[p256_n] */
  li        x2, 29
  la        x3, p256_n
  bn.lid    x2, 0(x3)

  /* store n to MOD WSR */
  bn.wsrw   0, w29

  /* 1st share (reduced rnd)
     rnd = w1 <= rnd mod n */
  bn.addm   w1, w1, w31

  /* 2nd share (k-rnd)
     w0 = w0 - w1 = k - rnd mod n */
  bn.subm   w0, w0, w1

  /* load field modulus p from dmem
     w29 <= p = dmem[p256_p] */
  li        x2, 29
  la        x3, p256_p
  bn.lid    x2, 0(x3)

  /* store modulus to MOD WSR */
  bn.wsrw   0, w29

  /* load lower 256 bit of Barrett constant u for modulus p from dmem
     w28 <= u = dmem[p256_u_p] */
  li        x2, 28
  la        x3, p256_u_p
  bn.lid    x2, 0(x3)

  /* load domain parameter b from dmem
     w27 <= b = dmem[p256_b] */
  li        x2, 27
  la        x3, p256_b
  bn.lid    x2, 0(x3)

  /* get randomized projective coodinates of curve point
     P = (x_p, y_p, z_p) = (w8, w9, w10) = (w6, w7, w26) =
     (x*z mod p, y*z mod p, z) */
  li        x10, 24
  jal       x1, fetch_proj_randomize
  bn.mov    w8, w6
  bn.mov    w9, w7
  bn.mov    w10, w26

  /* Init 2P, this will be used for the addition part in the double-and-add
     loop when the bit at the current index is 1 for both shares of the scalar.
     2P = (w3, w4, w5) <= (w11, w12, w13) <= 2*(w8, w9, w10) = 2*P */
  jal       x1, proj_double
  bn.mov    w3, w11
  bn.mov    w4, w12
  bn.mov    w5, w13

  /* init double-and-add with point in infinity
     Q = (w8, w9, w10) <= (0, 1, 0) */
  bn.mov    w8, w31
  bn.addi   w9, w31, 1
  bn.mov    w10, w31

  /* double-and-add loop with decreasing index */
  loopi     256, 32

    /* double point Q
       Q = (w11, w12, w13) <= 2*(w8, w9, w10) = 2*Q */
    jal       x1, proj_double

    /* re-fetch and randomize P again
       P = (w6, w7, w26) */
    jal       x1, fetch_proj_randomize

    /* probe if MSb of either of the two scalars (rnd or k-rnd) but not both
       is 1.
       If only one MSb is set, select P for addition
       If both MSbs are set, select 2P for addition
       (If neither MSB is set, also 2P will be selected but this will be
        discarded late) */
    bn.xor    w8, w0, w1

    /* P = (w8, w9, w10)
        <= (w0[255] xor w1[256])?P=(w6, w7, w26):2P=(w3, w4, w5) */
    bn.sel    w8, w6, w3, M
    bn.sel    w9, w7, w4, M
    bn.sel    w10, w26, w5, M

    /* save doubling result to survive follow-up subroutine call
       Q = (w2, w6, w7) <= (w11, w12, w13) */
    bn.mov    w2, w11
    bn.mov    w6, w12
    bn.mov    w7, w13

    /* add points
       Q+P = (w11, w12, w13) <= (w11, w12, w13) + (w8, w9, w10) */
    jal       x1, proj_add

    /* probe if MSb of either one or both of the two
       scalars (rnd or k-rnd) is 1.*/
    bn.or     w8, w0, w1

    /* select doubling result (Q) or addition result (Q+P)
       Q = w0[255] or w1[255]?Q_a=(w11, w12, w13):Q=(w2, w6, w7) */
    bn.sel    w8, w11, w2, M
    bn.sel    w9, w12, w6, M
    bn.sel    w10, w13, w7, M

    /* rotate both scalars left 1 bit */
    bn.rshi   w0, w0, w0 >> 255
    bn.rshi   w1, w1, w1 >> 255

    /* init regs with random numbers from URND */
    bn.wsrr   w11, 2
    bn.wsrr   w12, 2
    bn.wsrr   w13, 2

    /* get a fresh random number from URND and scale the coordinates of
       2P = (w3, w4, w5) (scaling each projective coordinate with same
       factor results in same point) */
    bn.wsrr   w2, 2

    /* w3 = w3 * w2 */
    bn.mov    w24, w3
    bn.mov    w25, w2
    jal       x1, mod_mul_256x256
    bn.mov    w3, w19

    /* w4 = w4 * w2 */
    bn.mov    w24, w4
    bn.mov    w25, w2
    jal       x1, mod_mul_256x256
    bn.mov    w4, w19

    /* w5 = w5 * w2 */
    bn.mov    w24, w5
    bn.mov    w25, w2
    jal       x1, mod_mul_256x256
    bn.mov    w5, w19

  /* convert back to affine coordinates
     R = (x_a, y_a) = (w11, w12) */
  jal       x1, proj_to_affine

  ret


/**
 * P-256 ECDSA signature generation
 *
 * returns the signature as the pair r, s with
 *         r = x_1  mod n
 *     and s = k^(-1)(msg + r*d)  mod n
 *         with x_1 being the affine x-coordinate of the curve point k*G,
 *                  where G is the curve's base point.
 *              k being a supplied secret random number,
 *              n being the order of the base point G of P-256,
 *              msg being the msg to be signed,
 *              d being the private key.
 *
 * This routine runs in constant time.
 *
 * Note: Some versions of the ECDSA spec suggest that msg must be reduced
 * modulo n (e.g. RFC 6979, section 2.4). However, for this implementation, it
 * is sufficient that msg < 2^256, because the message is multiplied with
 * k^(-1) mod n, and our Barrett multiplication implementation accepts any
 * operands a and b such that a * b < 2^256 * p and fully reduces the result.
 *
 * @param[in]  dmem[k]:   random secret scalar (256 bits)
 * @param[in]  dmem[rnd]: random number for blinding (256 bits)
 * @param[in]  dmem[msg]: message to be signed (256 bits)
 * @param[in]  dmem[r]:   dmem buffer for r component of signature (256 bits)
 * @param[in]  dmem[s]:   dmem buffer for s component of signature (256 bits)
 * @param[in]  dmem[d]:   private key d
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x16 to x23, w0 to w26
 * clobbered flag groups: FG0
 */
p256_sign:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* load secret random scalar k from dmem: w0 = dmem[k] */
  la        x16, k
  li        x2, 0
  bn.lid    x2, 0(x16)

  /* load random number for blinding from dmem: w1 = dmem[rnd] */
  la        x17, rnd
  li        x2, 1
  bn.lid    x2, 0(x17)

  /* scalar multiplication with base point
     (x_1, y_1) = (w11, w12) <= k*G = w0*(dmem[p256_gx], dmem[p256_gy]) */
  la        x21, p256_gx
  la        x22, p256_gy
  jal       x1, scalar_mult_int

  /* setup modulus n (curve order) and Barrett constant
     MOD <= w29 <= n = dmem[p256_n]; w28 <= u_n = dmem[p256_u_n]  */
  li        x2, 29
  la        x3, p256_n
  bn.lid    x2, 0(x3)
  bn.wsrw   0, w29
  li        x2, 28
  la        x3, p256_u_n
  bn.lid    x2, 0(x3)

  /* re-load secret random number k from dmem: w0 <= k = dmem[k] */
  la        x16, k
  li        x2, 0
  bn.lid    x2, 0(x16)

  /* modular multiplicative inverse of k
     w1 <= k^-1 mod n */
  jal       x1, mod_inv

  /* w19 = k^-1*d mod n; w24 = d = dmem[d] */
  la        x23, d
  li        x2, 24
  bn.lid    x2, 0(x23)
  bn.mov    w25, w1
  jal       x1, mod_mul_256x256

  /* w24 = r <= w11  mod n */
  bn.addm   w24, w11, w31

  /* store r of signature in dmem: dmem[r] <= r = w24 */
  la        x19, r
  li        x2, 24
  bn.sid    x2, 0(x19)

  /* w0 = w19 <= w24*w25 = w24*w19 = r*k^-1*d  mod n */
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256
  bn.mov    w0, w19

  /* load message from dmem: w24 = msg <= dmem[msg] */
  la        x18, msg
  li        x2, 24
  bn.lid    x2, 0(x18)

  /* w19 = k^-1*msg <= w25*w24 = w1*w24  mod n */
  bn.mov    w25, w1
  jal       x1, mod_mul_256x256

  /* w0 = s <= w19 + w0 = k^-1*msg + r*k^-1*d  mod n */
  bn.addm   w0, w19, w0

  /* store s of signature in dmem: dmem[s] <= s = w0 */
  la        x20, s
  li        x2, 0
  bn.sid    x2, 0(x20)

  ret


/**
 * P-256 scalar multiplication with base point G
 *
 * returns R = d*G = d*(x_g, y_g)
 *         with R and G being valid P-256 curve points in affine coordinates,
 *              furthermore G being the curves base point,
 *              d being a 256 bit scalar
 *
 * Performs a scalar multiplication of a scalar with the base point G of curve
 * P-256.
 * This routine runs in constant time.
 *
 * @param[in]     dmem[rnd]: random number for blinding (256 bits)
 * @param[in]     dmem[d]:   scalar d (256 bits)
 * @param[in,out] dmem[x]:   affine x-coordinate (256 bits)
 * @param[in,out] dmem[y]:   affine y-coordinate (256 bits)
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, x3, x16, x17, x21, x22, w0 to w26
 * clobbered flag groups: FG0
 */
p256_base_mult:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* load scalar d from dmem: w0 = dmem[d] */
  la        x16, d
  li        x2, 0
  bn.lid    x2, 0(x16)

  /* load random number for blinding from dmem: w1 = dmem[rnd] */
  la        x17, rnd
  li        x2, 1
  bn.lid    x2, 0(x17)

  /* call internal scalar multiplication routine
     R = (x_a, y_a) = (w11, w12) <= k*P = w0*P */
  la        x21, p256_gx
  la        x22, p256_gy
  jal       x1, scalar_mult_int

  /* store result (affine coordinates) in dmem
     dmem[x] <= x_a = w11
     dmem[y] <= y_a = w12 */
  li        x2, 11
  la        x21, x
  bn.sid    x2++, 0(x21)
  la        x22, y
  bn.sid    x2, 0(x22)

  ret


/**
 * Variable time modular multiplicative inverse computation
 *
 * Returns c <= a^(-1) mod m
 *         with a being a bigint of length 256 bit with a < m
 *              m being the modulus with a length of 256 bit
 *              c being a 256-bit result
 *
 * This routine implements the computation of the modular multiplicative
 * inverse based on the binary GCD or Stein's algorithm.
 * The implemented variant is based on the
 * "right-shift binary extended GCD" as it is described in section 3.1 of [1]
 * (Algorithm 1).
 * [1] https://doi.org/10.1155/ES/2006/32192
 *
 * Note that this is a variable time implementation. I.e. this routine will
 * show a data dependent timing and execution profile. Only use in situations
 * where a full white-box environment is acceptable.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w0: a, operand
 * @param[in]  MOD: m, modulus
 * @param[in]  w31: all-zero
 * @param[out]  w1: result c
 *
 * clobbered registers: x2, w2, w3, w4, w7
 * clobbered flag groups: FG0
 */
mod_inv_var:

  /* w2 = r = 0 */
  bn.mov    w2, w31

  /* w3 = s = 1 */
  bn.addi   w3, w31, 1

  /* w4 = u = MOD */
  bn.wsrr   w4, 0
  bn.wsrr   w7, 0

  /* w5 = v = w0 */
  bn.mov    w5, w0

  ebgcd_loop:
  /* test if u is odd */
  bn.or     w4, w4, w4
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 4
  bne       x2, x0, ebgcd_u_odd

  /* u is even: */
  /* w4 = u <= u/2 = w4 >> 1 */
  bn.rshi   w4, w31, w4 >> 1

  /* test if r is odd */
  bn.or     w2, w2, w2
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 4
  bne       x2, x0, ebgcd_r_odd

  /* r is even: */
  /* w2 = r <= r/2 = w2 >> 1 */
  bn.rshi   w2, w31, w2 >> 1
  jal       x0, ebgcd_loop

  ebgcd_r_odd:
  /* w2 = r <= (r + m)/2 = (w2 + w7) >> 1 */
  bn.add    w2, w7, w2
  bn.addc   w6, w31, w31
  bn.rshi   w2, w6, w2 >> 1
  jal       x0, ebgcd_loop

  ebgcd_u_odd:
  /* test if v is odd */
  bn.or     w5, w5, w5
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 4
  bne       x2, x0, ebgcd_uv_odd

  /* v is even: */
  /* w5 = v <= v/2 = w5 >> 1 */
  bn.rshi   w5, w31, w5 >> 1

  /* test if s is odd */
  bn.or     w3, w3, w3
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 4
  bne       x2, x0, ebgcd_s_odd

  /* s is even: */
  /* w3 = s <= s/2 = w3 >> 1 */
  bn.rshi   w3, w31, w3 >> 1
  jal       x0, ebgcd_loop

  ebgcd_s_odd:
  /* w3 = s <= (s + m)/2 = (w3 + w7) >> 1 */
  bn.add    w3, w7, w3
  bn.addc   w6, w31, w31
  bn.rshi   w3, w6, w3 >> 1
  jal       x0, ebgcd_loop

  ebgcd_uv_odd:
  /* test if v >= u */
  bn.cmp    w5, w4
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  beq       x2, x0, ebgcd_v_gte_u

  /* u > v: */
  /* w2 = r <= r - s = w2 - w3; if (r < 0): r <= r + m */
  bn.subm   w2, w2, w3

  /* w4 = u <= u - v = w4 - w5 */
  bn.sub    w4, w4, w5
  jal       x0, ebgcd_loop

  ebgcd_v_gte_u:
  /* w3 = s <= s - r = w3 - w2; if (s < 0) s <= s + m */
  bn.subm   w3, w3, w2

  /* w5 = v <= v - u = w5 - w4 */
  bn.sub    w5, w5, w4

  /* if v > 0 go back to start of loop */
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 8
  beq       x2, x0, ebgcd_loop

  /* v <= 0: */
  /* if (r > m): w1 = a = r - m = w2 - MOD else: w1 = a = r = w2 */
  bn.addm   w1, w2, w31

  ret


/**
 * P-256 ECDSA signature verification
 *
 * returns the affine x-coordinate of
 *         (x1, y1) = u1*G + u2*Q
 *         with u1 = z*s^-1 mod n  and  u2 = r*s^-1 mod n
 *         with G being the curve's base point,
 *              z being the message
 *              r, s being the signature
 *              Q being the public key.
 *
 * The routine computes the x1 coordinate and places it in dmem. x1 will be
 * reduced (mod n), however, the final comparison has to be performed on the
 * host side. The signature is valid if x1 == r.
 * This routine runs in variable time.
 *
 * @param[in]  dmem[msg]: message to be verified (256 bits)
 * @param[in]  dmem[r]:   r component of signature (256 bits)
 * @param[in]  dmem[s]:   s component of signature (256 bits)
 * @param[in]  dmem[x]:   affine x-coordinate of public key (256 bits)
 * @param[in]  dmem[y]:   affine y-coordinate of public key (256 bits)
 * @param[out] dmem[x_r]: dmem buffer for reduced affine x_r-coordinate (x_1)
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, x3, x13, x14, x17 to x24, w0 to w25
 * clobbered flag groups: FG0
 */
p256_verify:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* load domain parameter b from dmem
     w27 <= b = dmem[p256_b] */
  li        x2, 27
  la        x3, p256_b
  bn.lid    x2, 0(x3)

  /* load r of signature from dmem: w24 = r = dmem[r] */
  la        x19, r
  li        x2, 11
  bn.lid    x2, 0(x19)

  /* setup modulus n (curve order) and Barrett constant
     MOD <= w29 <= n = dmem[p256_n]; w28 <= u_n = dmem[p256_u_n]  */
  li        x2, 29
  la        x3, p256_n
  bn.lid    x2, 0(x3)
  bn.wsrw   0, w29
  li        x2, 28
  la        x3, p256_u_n
  bn.lid    x2, 0(x3)

  /* load s of signature from dmem: w0 = s = dmem[s] */
  la        x20, s
  bn.lid    x0, 0(x20)

  /* goto 'fail' if w0 == w31 <=> s == 0 */
  bn.cmp    w0, w31
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 8
  bne       x2, x0, fail

  /* goto 'fail' if w0 >= w29 <=> s >= n */
  bn.cmp    w0, w29
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  beq       x2, x0, fail

  /* w1 = s^-1  mod n */
  jal       x1, mod_inv_var

  /* load r of signature from dmem: w24 = r = dmem[r] */
  la        x19, r
  li        x2,  24
  bn.lid    x2, 0(x19)

  /* goto 'fail' if w24 == w31 <=> r == 0 */
  bn.cmp    w24, w31
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 8
  bne       x2, x0, fail

  /* goto 'fail' if w0 >= w29 <=> r >= n */
  bn.cmp    w24, w29
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  beq       x2, x0, fail

  /* w25 = s^-1 = w1 */
  bn.mov    w25, w1

  /* u2 = w0 = w19 <= w24*w25 = r*s^-1 mod n */
  jal       x1, mod_mul_256x256
  bn.mov    w0, w19

  /* load message, w24 = msg = dmem[msg] */
  la        x18, msg
  li        x2, 24
  bn.lid    x2, 0(x18)

  /* u1 = w1 = w19 <= w24*w25 = w24*w1 = msg*s^-1 mod n */
  bn.mov    w25, w1
  jal       x1, mod_mul_256x256
  bn.mov    w1, w19

  /* setup modulus p and Barrett constant */
  li        x2, 29
  la        x3, p256_p
  bn.lid    x2, 0(x3)
  bn.wsrw   0, w29
  li        x2, 28
  la        x3, p256_u_p
  bn.lid    x2, 0(x3)

  /* load public key Q from dmem and use in projective form (set z to 1)
     Q = (w11, w12, w13) = (dmem[x], dmem[y], 1) */
  li        x2, 11
  la        x21, x
  bn.lid    x2++, 0(x21)
  la        x22, y
  bn.lid    x2, 0(x22)
  bn.addi   w13, w31, 1

  /* load base point G and use in projective form (set z to 1)
     G = (w8, w9, w10) = (x_g, y_g, 1) */
  li        x13, 8
  la        x23, p256_gx
  bn.lid    x13, 0(x23)
  li        x14, 9
  la        x24, p256_gy
  bn.lid    x14, 0(x24)
  bn.addi   w10, w31, 1

  /* The rest of the routine implements a variable time double-and-add
     algorithm. For the signature verification we need to compute the point
     C = (x1, y1) = u_1*G + u_2*Q. This can be done in a single
     double-and-add routine by using Shamir's Trick. */

  /* G+Q = (w3,w4,w5) = (w11,w12,w13) = (w8,w9,w10) (+) (w11,w12,w13) */
  jal       x1, proj_add
  bn.mov    w3, w11
  bn.mov    w4, w12
  bn.mov    w5, w13

  /* w2 = u_2 & u_0 = w0 & w1*/
  bn.and    w2, w0, w1

  /* init double and add algorithm with (0, 1, 0) */
  bn.mov    w11, w31
  bn.addi   w12, w31, 1
  bn.mov    w13, w31

  /* main loop with dicreasing index i (i=255 downto 0) */
  loopi     256, 31

    /* always double: C = (w11,w12,w13) <= 2 (*) C = 2 (*) (w11,w12,w13) */
    bn.mov    w8, w11
    bn.mov    w9, w12
    bn.mov    w10, w13
    jal       x1, proj_add

    /* if either  u_1[i] == 0 or u_2[i] == 0 jump to 'no_both' */
    bn.add    w2, w2, w2
    csrrs     x2, 0x7c0, x0
    andi      x2, x2, 1
    beq       x2, x0, no_both

    /* both bits at current index (u1[i] and u2[i]) are set:
       do C <= C + (P + Q) and jump to end */
    bn.mov    w8, w3
    bn.mov    w9, w4
    bn.mov    w10, w5
    jal       x1, proj_add
    jal       x0, no_q

    /* either u1[i] or u2[i] is set, but not both */
    no_both:

    /* if u2[i] is not set jump to 'no_g' */
    bn.add    w6, w0, w0
    csrrs     x2, 0x7c0, x0
    andi      x2, x2, 1
    beq       x2, x0, no_g

    /* u2[i] is set: do C <= C + Q */
    bn.lid    x13, 0(x21)
    bn.lid    x14, 0(x22)
    bn.addi   w10, w31, 1
    jal       x1, proj_add

    no_g:
    /* if u1[i] is not set jump to 'no_q' */
    bn.add    w6, w1, w1
    csrrs     x2, 0x7c0, x0
    andi      x2, x2, 1
    beq       x2, x0, no_q

    /* load base point x-coordinate
      w8 <= g_x = dmem [p256_gx]; w9 <= g_y = dmem[p256_gy] */
    bn.lid    x13, 0(x23)
    bn.lid    x14, 0(x24)

    /* u1[i] is set: do C <= C + G */
    bn.addi   w10, w31, 1
    jal       x1, proj_add

    no_q:
    /* left shift w0 and w1 to decrease index */
    bn.add    w0, w0, w0
    bn.add    w1, w1, w1

  /* compute inverse of z-coordinate: w1 = z_c^-1  mod p */
  bn.mov    w0, w13
  jal       x1, mod_inv_var

  /* convert x-coordinate of C back to affine: x1 = x_c * z_c^-1  mod p */
  bn.mov    w24, w1
  bn.mov    w25, w11
  jal       x1, mod_mul_256x256

  /* final reduction: w24 = x1 <= x1 mod n */
  la        x3, p256_n
  bn.lid    x0, 0(x3)
  bn.wsrw   0, w0
  bn.subm   w24, w19, w31

  fail:
  /* store affine x-coordinate in dmem: dmem[x_r] = w24 = x_r */
  la        x17, x_r
  li        x2, 24
  bn.sid    x2, 0(x17)

  ret


/**
 * Externally callable wrapper for P-256 scalar point multiplication
 *
 * returns R = k*P = k*(x_p, y_p, z_p)
 *         with R, P being valid P-256 curve points in projective form,
 *              k being a 256 bit scalar.
 *
 * Sets up context and calls internal scalar multiplication routine.
 * This routine runs in constant time.
 *
 * @param[in]      dmem[k]:   scalar k (256 bits)
 * @param[in]      dmem[rnd]: random number for blinding (256 bits)
 * @param[in,out]  dmem[x]:   affine x-coordinate in dmem
 * @param[in,out]  dmem[y]:   affine y-coordinate in dmem
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x16, x17, x21, x22, w0 to w25
 * clobbered flag groups: FG0
 */
p256_scalar_mult:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* load private key d from dmem: w0 = dmem[d] */
  la        x16, d
  li        x2, 0
  bn.lid    x2, 0(x16)

  /* load random number for blinding from dmem: w1 = dmem[rnd] */
  la        x17, rnd
  li        x2, 1
  bn.lid    x2, 0(x17)

  /* call internal scalar multiplication routine
     R = (x_a, y_a) = (w11, w12) <= k*P = w0*P */
  la        x21, x
  la        x22, y
  jal       x1, scalar_mult_int

  /* store result (affine coordinates) in dmem
     dmem[x] <= x_a = w11
     dmem[y] <= y_a = w12 */
  li        x2, 11
  bn.sid    x2++, 0(x21)
  bn.sid    x2, 0(x22)

  ret

.section .data

/* P-256 domain parameter b */
.globl p256_b
.balign 32
p256_b:
  .word 0x27d2604b
  .word 0x3bce3c3e
  .word 0xcc53b0f6
  .word 0x651d06b0
  .word 0x769886bc
  .word 0xb3ebbd55
  .word 0xaa3a93e7
  .word 0x5ac635d8

/* P-256 domain parameter p (modulus) */
.globl p256_p
.balign 32
p256_p:
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000001
  .word 0xffffffff

/* Barrett constant u for modulus p */
.globl p256_u_p
.balign 32
p256_u_p:
  .word 0x00000003
  .word 0x00000000
  .word 0xffffffff
  .word 0xfffffffe
  .word 0xfffffffe
  .word 0xfffffffe
  .word 0xffffffff
  .word 0x00000000

/* P-256 domain parameter n (order of base point) */
.globl p256_n
.balign 32
p256_n:
  .word 0xfc632551
  .word 0xf3b9cac2
  .word 0xa7179e84
  .word 0xbce6faad
  .word 0xffffffff
  .word 0xffffffff
  .word 0x00000000
  .word 0xffffffff

/* Barrett constant u for n */
.globl p256_u_n
.balign 32
p256_u_n:
  .word 0xeedf9bfe
  .word 0x012ffd85
  .word 0xdf1a6c21
  .word 0x43190552
  .word 0xffffffff
  .word 0xfffffffe
  .word 0xffffffff
  .word 0x00000000

/* P-256 basepoint G affine x-coordinate */
.globl p256_gx
.balign 32
p256_gx:
  .word 0xd898c296
  .word 0xf4a13945
  .word 0x2deb33a0
  .word 0x77037d81
  .word 0x63a440f2
  .word 0xf8bce6e5
  .word 0xe12c4247
  .word 0x6b17d1f2

/* P-256 basepoint G affine y-coordinate */
.globl p256_gy
.balign 32
p256_gy:
  .word 0x37bf51f5
  .word 0xcbb64068
  .word 0x6b315ece
  .word 0x2bce3357
  .word 0x7c0f9e16
  .word 0x8ee7eb4a
  .word 0xfe1a7f9b
  .word 0x4fe342e2

.section .bss

/* random scalar k */
.balign 32
.weak k
k:
  .zero 32

/* randomness for blinding */
.balign 32
.weak rnd
rnd:
  .zero 32

/* message digest */
.balign 32
.weak msg
msg:
  .zero 32

/* signature R */
.balign 32
.weak r
r:
  .zero 32

/* signature S */
.balign 32
.weak s
s:
  .zero 32

/* public key x-coordinate */
.balign 32
.weak x
x:
  .zero 32

/* public key y-coordinate */
.balign 32
.weak y
y:
  .zero 32

/* private key d */
.balign 32
.weak d
d:
  .zero 32

/* verification result x_r (aka x_1) */
.balign 32
.weak x_r
x_r:
  .zero 32
