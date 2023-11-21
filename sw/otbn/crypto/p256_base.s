/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_p256.c
 */

.globl p256_scalar_mult
.globl p256_base_mult
.globl p256_generate_k
.globl p256_generate_random_key
.globl p256_key_from_seed
.globl trigger_fault_if_fg0_z
.globl mod_mul_256x256
.globl mod_mul_320x128
.globl scalar_mult_int
.globl proj_add
.globl proj_to_affine

/* Exposed only for testing or SCA purposes. */
.globl mod_inv

.text

/**
 * Trigger a fault if the FG0.Z flag is 1.
 *
 * If the flag is 1, then this routine will trigger an `ILLEGAL_INSN` error and
 * abort the OTBN program. If the flag is 0, the routine will essentially do
 * nothing.
 *
 * NOTE: Be careful when calling this routine that the FG0.Z flag is not
 * sensitive; since aborting the program will be quicker than completing it,
 * the flag's value is likely clearly visible to an attacker through timing.
 *
 * @param[in]    w31: all-zero
 * @param[in]  FG0.Z: boolean indicating fault condition
 *
 * clobbered registers: x2
 * clobbered flag groups: none
 */
trigger_fault_if_fg0_z:
  /* Read the FG0.Z flag (position 3).
       x2 <= FG0.Z */
  csrrw     x2, FG0, x0
  andi      x2, x2, 8
  srli      x2, x2, 3

  /* Subtract FG0.Z from 0.
       x2 <= 0 - x2 = FG0.Z ? 2^32 - 1 : 0 */
  sub       x2, x0, x2

  /* The `bn.lid` instruction causes an `BAD_DATA_ADDR` error if the
     memory address is out of bounds. Therefore, if FG0.Z is 1, this
     instruction causes an error, but if FG0.Z is 0 it simply loads the word at
     address 0 into w31. */
  li         x3, 31
  bn.lid     x3, 0(x2)

  /* If we get here, the flag must have been 0. Restore w31 to zero and return.
       w31 <= 0 */
  bn.xor     w31, w31, w31

  ret

/**
 * Reduce a 512-bit value by a 256-bit P-256 modulus (either n or p).
 *
 * Returns c = a mod m
 *
 * Expects a 512 bit input, a 256 bit modulus and pre-computed parameter u for
 * Barrett reduction (usually greek mu in literature). u is expected without
 * the leading 1 at bit 256. u has to be pre-computed as u = floor(2^512/p).
 * This guarantees that u > 2^256, however, in order for u to be at most
 * 2^257-1, it has to be ensured that m >= 2^255 + 1.
 *
 * This implementation mostly follows the description in the
 * "Handbook of Applied Cryptography" in Algorithm 14.42.
 * Differences:
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
 * proven that a single subtraction is sufficient. The following condition is
 * sufficient (although potentially not necessary):
 *   b * (b^2k mod m) + mu <= b^(k+1)
 *
 * For OTBN with a 256-bit modulus, we have b=2^256 and k=1, so this is:
 *   2^256 * (2^512 mod m) + mu <= 2^512
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w19,w20]: a, input (512 bits) such that a < 2^256 * m
 * @param[in]  w22: correction factor, msb(a) * u
 * @param[in]  w29: m, modulus, curve order n or finite field modulus p
 * @param[in]  w28: u, lower 256 bit of Barrett constant for m
 * @param[in]  w31: all-zero
 * @param[in]  MOD: m, modulus
 * @param[out]  w19: c, result
 *
 * clobbered registers: w19, w20, w21, w22, w23, w24, w25
 * clobbered flag groups: FG0
 */
p256_reduce:
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
 * 256-bit modular multiplication for P-256 coordinate and scalar fields.
 *
 * Returns c = a * b mod m
 *
 * Expects two 256 bit operands, 256 bit modulus and pre-computed parameter u
 * for Barrett reduction (usually greek mu in literature). See the note above
 * `p256_reduce` for details.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w24: a, first 256 bit operand (a * b < 2^256 * p)
 * @param[in]  w25: b, second 256 bit operand (a * b < 2^256 * p)
 * @param[in]  w29: m, modulus, curve order n or finite field modulus p
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

  /* Store correction factor to compensate for later neglected MSb of x.
     x is 512 bit wide and therefore the 255 bit right shifted version q1
     (below) contains 257 bit. Bit 256 of q1 is neglected to allow using a
     256x256 multiplier. For the MSb of x being set we temporary store u
     (or zero) here to be used in a later constant time correction of a
     multiplication with u. Note that this requires the MSb flag being carried
     over from the multiplication routine. */
  bn.sel    w22, w28, w31, M

  /* Reduce product modulo m. */
  jal       x1, p256_reduce

  ret

/**
 * 320- by 128-bit modular multiplication for P-256 coordinate and scalar fields.
 *
 * Returns c = a * b mod m
 *
 * Expects two operands, 256 bit modulus and pre-computed parameter u
 * for Barrett reduction (usually greek mu in literature). See the note above
 * `p256_reduce` for details.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w24: a0, low part of 320-bit operand a (256 bits)
 * @param[in]  w25: a1, high part of 320-bit operand a (64 bits)
 * @param[in]  w26: b, second operand (128 bits)
 * @param[in]  w29: m, modulus, curve order n or finite field modulus p
 * @param[in]  w28: u, lower 256 bit of Barrett constant for curve P-256
 * @param[in]  w31: all-zero
 * @param[in]  MOD: p, modulus of P-256 underlying finite field
 * @param[out]  w19: c, result
 *
 * clobbered registers: w19, w20, w21, w22, w23, w24, w25
 * clobbered flag groups: FG0
 */
mod_mul_320x128:
  /* Compute the integer product of the operands x = a * b
     x = [w20, w19] = a * b = w24 * w25
     => max. length of x: 448 bit */
  bn.mulqacc.z          w24.0, w26.0, 0
  bn.mulqacc            w24.0, w26.1, 64
  bn.mulqacc.so  w19.L, w24.1, w26.0, 64
  bn.mulqacc            w24.1, w26.1, 0
  bn.mulqacc            w24.2, w26.0, 0
  bn.mulqacc            w24.2, w26.1, 64
  bn.mulqacc.so  w19.U, w24.3, w26.0, 64
  bn.mulqacc            w24.3, w26.1, 0
  bn.mulqacc            w25.0, w26.0, 0
  bn.mulqacc.wo    w20, w25.0, w26.1, 64

  /* Store correction factor to compensate for later neglected MSb of x.
     x is 512 bit wide and therefore the 255 bit right shifted version q1
     (below) contains 257 bit. Bit 256 of q1 is neglected to allow using a
     256x256 multiplier. For the MSb of x being set we temporary store u
     (or zero) here to be used in a later constant time correction of a
     multiplication with u. Note that this requires the MSb flag being carried
     over from the multiplication routine. */
  bn.sel    w22, w28, w31, M

  /* Reduce product modulo m. */
  jal       x1, p256_reduce

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
 * @param[out]  w14: z^-1, modular inverse of the projective z-coordinate
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
 * For exponentiation we use a standard, variable time square and multiply
 * algorithm. (The timing varies based on the modulus alone, not the input x,
 * so it is safe to use for a non-secret modulus and a secret operand).
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
    csrrs     x2, FG0, x0
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
 * @param[out] w14: x, projective x-coordinate
 * @param[out] w15: y, projective y-coordinate
 * @param[out] w16: z, random projective z-coordinate
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the scaled projective y-coordinate.
 *
 * clobbered registers: w14 to w16, w19 to w26
 * clobbered flag groups: FG0
 */
fetch_proj_randomize:

  /* get random number from URND */
  bn.wsrr   w16, 2 /* URND */

  /* reduce random number
     w16 = z <= w16 mod p */
  bn.addm   w16, w16, w31

  /* fetch x-coordinate from dmem
     w24 = x_a <= dmem[x22] = dmem[dptr_x] */
  bn.lid    x10, 0(x21)

  /* scale x-coordinate
     w14 = x <= w24*w16 = x_a*z  mod p */
  bn.mov    w25, w16
  jal       x1, mod_mul_256x256
  bn.mov    w14, w19

  /* fetch y-coordinate from dmem
     w24 = y_a <= dmem[x22] = dmem[dptr_y] */
  bn.lid    x10, 0(x22)

  /* scale y-coordinate
     w15 = y <= w24*w16 = y_a*z  mod p */
  bn.mov    w25, w16
  jal       x1, mod_mul_256x256
  bn.mov    w15, w19

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
 *
 * The routine receives the scalar in two shares k0, k1 such that
 *   k = (k0 + k1) mod n
 * The loop operates on both shares in parallel, computing (k0 + k1) * P as
 * follows:
 *  Q = (0, 1, 0) # origin
 *  for i in 319..0:
 *    Q = 2 * Q
 *    A = if (k0[i] ^ k1[i]) then P else 2P
 *    B = Q + A
 *    Q = if (k0[i] | k1[i]) then B else Q
 *
 *
 * Each share k0/k1 is 320 bits, even though it represents a 256-bit value.
 * This is a side-channel protection measure.
 *
 * @param[in]  x21: dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]  x22: dptr_y, pointer to affine y-coordinate in dmem
 * @param[in]  w0: lower 256 bits of k0, first share of scalar
 * @param[in]  w1: upper 64 bits of k0, first share of scalar
 * @param[in]  w2: lower 256 bits of k1, second share of scalar
 * @param[in]  w3: upper 64 bits of k1, second share of scalar
 * @param[in]  w27: b, curve domain parameter
 * @param[in]  w31: all-zero
 * @param[in]  MOD: p, modulus, 2^256 > p > 2^255.
 * @param[out]  w8: x, x-coordinate of curve point (projective)
 * @param[out]  w9: y, y-coordinate of curve point (projective)
 * @param[out]  w10: z, z-coordinate of curve point (projective)
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x10, w0 to w30
 * clobbered flag groups: FG0
 */
scalar_mult_int:

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
     P = (x_p, y_p, z_p) = (w8, w9, w10) = (w14, w15, w16) =
     (x*z mod p, y*z mod p, z) */
  li        x10, 24
  jal       x1, fetch_proj_randomize
  bn.mov    w8, w14
  bn.mov    w9, w15
  bn.mov    w10, w16

  /* Init 2P, this will be used for the addition part in the double-and-add
     loop when the bit at the current index is 1 for both shares of the scalar.
     2P = (w4, w5, w6) <= (w11, w12, w13) <= 2*(w8, w9, w10) = 2*P */
  jal       x1, proj_double
  bn.mov    w4, w11
  bn.mov    w5, w12
  bn.mov    w6, w13

  /* init double-and-add with point in infinity
     Q = (w8, w9, w10) <= (0, 1, 0) */
  bn.mov    w8, w31
  bn.addi   w9, w31, 1
  bn.mov    w10, w31

  /* Shift shares of k so their MSBs are in the most significant position of a
     word.
       w0,w1 <= [w0, w1] << 192 = k0 << 192
       w2,w3 <= [w2, w3] << 192 = k1 << 192 */
  bn.rshi   w1, w1, w0 >> 64
  bn.rshi   w0, w0, w31 >> 64
  bn.rshi   w3, w3, w2 >> 64
  bn.rshi   w2, w2, w31 >> 64

  /* double-and-add loop with decreasing index */
  loopi     320, 34

    /* double point Q
       Q = (w11, w12, w13) <= 2*(w8, w9, w10) = 2*Q */
    jal       x1, proj_double

    /* re-fetch and randomize P again
       P = (w14, w15, w16) */
    jal       x1, fetch_proj_randomize

    /* probe if MSb of either of the two scalars (k0 or k1) but not both is 1.
       - If only one MSb is set, select P for addition
       - If both MSbs are set, select 2P for addition
       - If neither MSB is set, also 2P will be selected but this will be
         discarded later */
    bn.xor    w20, w1, w3

    /* N.B. The M bit here is secret. For side channel protection in the
       selects below, it is vital that neither option is equal to the
       destionation register (e.g. bn.sel w0, w0, w1). In this case, the
       hamming distance from the destination's previous value to its new value
       will be 0 in one of the cases and potentially reveal M.

       P = (w8, w9, w10)
        <= (w0[255] xor w1[255])?P=(w14, w15, w16):2P=(w4, w5, w6) */
    bn.sel    w8, w14, w4, M
    bn.sel    w9, w15, w5, M
    bn.sel    w10, w16, w6, M

    /* save doubling result to survive follow-up subroutine call
       Q = (w7, w26, w30) <= (w11, w12, w13) */
    bn.mov    w7, w11
    bn.mov    w26, w12
    bn.mov    w30, w13

    /* add points
       Q+P = (w11, w12, w13) <= (w11, w12, w13) + (w8, w9, w10) */
    jal       x1, proj_add

    /* probe if MSb of either one or both of the two
       scalars (k0 or k1) is 1.*/
    bn.or     w20, w1, w3

    /* N.B. As before, the select instructions below must use distinct
       source/destination registers to avoid revealing M.

       Select doubling result (Q) or addition result (Q+P)
         Q = w0[255] or w1[255]?Q_a=(w11, w12, w13):Q=(w7, w26, w30) */
    bn.sel    w8, w11, w7, M
    bn.sel    w9, w12, w26, M
    bn.sel    w10, w13, w30, M

    /* Shift both scalars left 1 bit. */
    bn.rshi   w1, w1, w0 >> 255
    bn.rshi   w0, w0, w31 >> 255
    bn.rshi   w3, w3, w2 >> 255
    bn.rshi   w2, w2, w31 >> 255

    /* init regs with random numbers from URND */
    bn.wsrr   w11, 2
    bn.wsrr   w12, 2
    bn.wsrr   w13, 2

    /* get a fresh random number from URND and scale the coordinates of
       2P = (w3, w4, w5) (scaling each projective coordinate with same
       factor results in same point) */
    bn.wsrr   w7, 2

    /* w4 = w4 * w7 */
    bn.mov    w24, w4
    bn.mov    w25, w7
    jal       x1, mod_mul_256x256
    bn.mov    w4, w19

    /* w5 = w5 * w7 */
    bn.mov    w24, w5
    bn.mov    w25, w7
    jal       x1, mod_mul_256x256
    bn.mov    w5, w19

    /* w6 = w6 * w7 */
    bn.mov    w24, w6
    bn.mov    w25, w7
    jal       x1, mod_mul_256x256
    bn.mov    w6, w19

  /* Check if the z-coordinate of Q is 0. If so, fail; this represents the
     point at infinity and means the scalar was zero mod n, which likely
     indicates a fault attack.

     FG0.Z <= if (w10 == 0) then 1 else 0 */
  bn.cmp    w10, w31
  jal       x1, trigger_fault_if_fg0_z

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
 *
 * This routine assumes that the scalar d is provided in two shares, d0 and d1,
 * where:
 *   d = (d0 + d1) mod n
 *
 * The shares d0 and d1 are up to 320 bits each to provide extra redundancy.
 *
 * This routine runs in constant time.
 *
 * @param[in]   dmem[d0]:  first share of scalar d (320 bits)
 * @param[in]   dmem[d1]:  second share of scalar d (320 bits)
 * @param[out]  dmem[x]:   affine x-coordinate (256 bits)
 * @param[out]  dmem[y]:   affine y-coordinate (256 bits)
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, x3, x16, x17, x21, x22, w0 to w26
 * clobbered flag groups: FG0
 */
p256_base_mult:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* Load first share of secret key d from dmem.
       w0,w1 = dmem[d0] */
  la        x16, d0
  li        x2, 0
  bn.lid    x2, 0(x16++)
  li        x2, 1
  bn.lid    x2, 0(x16)

  /* Load second share of secret key d from dmem.
       w2,w3 = dmem[d1] */
  la        x16, d1
  li        x2, 2
  bn.lid    x2, 0(x16++)
  li        x2, 3
  bn.lid    x2, 0(x16)

  /* call internal scalar multiplication routine
     R = (x_p, y_p, z_p) = (w8, w9, w10) <= d*P = (w0 + w1)*P */
  la        x21, p256_gx
  la        x22, p256_gy
  jal       x1, scalar_mult_int

  /* Convert masked result back to affine coordinates.
     R = (x_a, y_a) = (w11, w12) */
  jal       x1, proj_to_affine

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
 * Externally callable wrapper for P-256 scalar point multiplication
 *
 * Calculates R = k*P = k*(x_a, y_a)
 *         with R, P being valid P-256 curve points in affine form,
 *         k being a 256 bit scalar. The x coordinate of R is
 *         arithmetically masked.
 * Returns the masked x coordinate of R and the corresponding mask.
 *
 * This routine assumes that the scalar k is provided in two shares, k0 and k1,
 * where:
 *   k = (k0 + k1) mod n
 *
 * Sets up context and calls internal scalar multiplication routine.
 * This routine runs in constant time.
 *
 * @param[in]      dmem[k0]:  first share of scalar k (320 bits)
 * @param[in]      dmem[k1]:  second share of scalar k (320 bits)
 * @param[in]      dmem[x]:   affine x-coordinate in dmem
 * @param[in]      dmem[y]:   affine y-coordinate in dmem
 * @param[out]     dmem[x]:   affine arithmetically masked x-coordinate in dmem
 * @param[out]     dmem[y]:   arithmetic mask for x coordinate in dmem
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

  /* Load first share of secret key k from dmem.
       w0,w1 = dmem[k0] */
  la        x16, k0
  li        x2, 0
  bn.lid    x2, 0(x16++)
  li        x2, 1
  bn.lid    x2, 0(x16)

  /* Load second share of secret key k from dmem.
       w2,w3 = dmem[k1] */
  la        x16, k1
  li        x2, 2
  bn.lid    x2, 0(x16++)
  li        x2, 3
  bn.lid    x2, 0(x16)

  /* Call internal scalar multiplication routine.
     Returns point in projective coordinates.
     R = (x, y, z) = (w8, w9, w10) <= k*P = w0*P */
  la        x21, x
  la        x22, y
  jal       x1, scalar_mult_int

  /* Arithmetic masking:
   1. Generate a random mask
   2. Subtract masks from projective x coordinate
      (x, y, z) -> ((x - m) mod p,
                     y,
                     z)
   3. Convert masked curve point back to affine
      form.
   4. Multiply mask with z^-1 for use in
      affine space. */

  /* Fetch a fresh random number as mask.
       w2 <= URND() */
  bn.wsrr   w2, 0x2 /* URND */

  /* Subtract random mask from x coordinate of
     projective point.
     The subtraction has to be done within the underlying
     finite field -> mod p.
     w8 = (w8 - w2) mod p */
  bn.subm    w8, w8, w2

  /* Convert masked result back to affine coordinates.
     R = (x_a, y_a) = (w11, w12) */
  jal       x1, proj_to_affine

  /* Store result (masked affine x-coordinate) in DMEM.
     Y-coordinate not needed, will be overwritten with
     mask value below.
     dmem[x] <= x_a = w11 */
  li        x2, 11
  bn.sid    x2, 0(x21)

  /* Get modular inverse z^-1 of projective z coordinate
     and multiply the random masks with z^-1 to
     also convert them into affine space. */

  /* Load barrett constant as input for
     mod_mul_256x256.
     w28 = dmem[p256_u_p] */
  li        x2, 28
  la        x4, p256_u_p
  bn.lid    x2, 0(x4)

  /* Get field modulus p.
     w29 <= MOD() */
  bn.wsrr   w29, 0x00 /* MOD */

  /* Move z^-1 and x coordinate mask to
     mod_mul_256x256 input WDRs.
     z^-1 is still stored in w14 from previous
     proj_to_affine call.
     w25 <= w14 = z^-1
     w24 <= w2 = m_x */
  bn.mov    w25, w14
  bn.mov    w24, w2

  /* Compute modular multiplication of m_x and z^-1.
     w19 = w24 * w25 mod w29 = m_x * z^-1 mod p */
  jal       x1, mod_mul_256x256

  /* Store "affine" mask to DMEM. Use the y-coordinate
     to save memory (not needed afterwards)
     dmem[y] <= w19 = m_x * z^-1 mod p */
  li        x2, 19
  bn.sid    x2, 0(x22)

  ret

/**
 * Generate a nonzero random value in the scalar field.
 *
 * Returns t, a random value that is nonzero mod n, in shares.
 *
 * This follows a modified version of the method in FIPS 186-4 sections B.4.1
 * and B.5.1 for generation of secret scalar values d and k. The computation
 * in FIPS 186-4 is:
 *   seed = RBG(seedlen) // seedlen >= 320
 *   return (seed mod (n-1)) + 1
 *
 * The important features here are that (a) the seed is at least 64 bits longer
 * than n in order to minimize bias after the reduction and (b) the resulting
 * scalar is guaranteed to be nonzero.
 *
 * We deviate from FIPS a little bit here because for side-channel protection,
 * we do not want to fully reduce the seed modulo (n-1) or combine the shares.
 * Instead, we do the following:
 *   seed0 = RBG(320)
 *   seed1 = RBG(320)
 *   x = URND(127) + 1 // random value for masking
 *   if (seed0 * x + seed1 * x) mod n == 0:
 *     retry
 *   return seed0, seed1
 *
 * Essentially, we get two independent seeds and interpret these as additive
 * shares of the scalar t = (seed0 + seed1) mod n. Then, we need to ensure t is
 * nonzero. Multiplying each share with a random masking parameter allows us to
 * safely add them, and then check if this result is 0; if it is, then t must
 * be 0 mod n and we need to retry.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w31:  all-zero
 * @param[out] w15,w16:  first share of secret scalar t (320 bits)
 * @param[out] w17,w18:  second share of secret scalar t (320 bits)
 *
 * clobbered registers: x2, x3, x20, w12 to w29
 * clobbered flag groups: FG0
 */
p256_random_scalar:
  /* Load the curve order n.
     w29 <= dmem[p256_n] = n */
  li        x2, 29
  la        x3, p256_n
  bn.lid    x2, 0(x3)

  /* Copy n into the MOD register. */
  bn.wsrw   0, w29

  /* Load Barrett constant for n.
     w28 <= u_n = dmem[p256_u_n]  */
  li        x2, 28
  la        x3, p256_u_n
  bn.lid    x2, 0(x3)

  random_scalar_retry:
  /* Obtain 768 bits of randomness from RND. */
  bn.wsrr   w15, 0x1 /* RND */
  bn.wsrr   w16, 0x1 /* RND */
  bn.wsrr   w17, 0x1 /* RND */

  /* XOR with bits from URND, just in case there's any vulnerability in EDN
     that lets the attacker recover bits before they reach OTBN. */
  bn.wsrr   w20, 0x2 /* URND */
  bn.xor    w15, w15, w20
  bn.wsrr   w20, 0x2 /* URND */
  bn.xor    w16, w16, w20
  bn.wsrr   w20, 0x2 /* URND */
  bn.xor    w17, w17, w20

  /* Shift bits to get 320-bit seeds.
     w18 <= w16[255:192]
     w16 <= w16[63:0] */
  bn.rshi   w18, w31, w16 >> 192
  bn.rshi   w20, w16, w31 >> 64
  bn.rshi   w16, w20, w31 >> 192

  /* Generate a random masking parameter.
     w14 <= URND(127) + 1 = x */
  bn.wsrr   w14, 0x2 /* URND */
  bn.addi   w14, w14, 1

  /* w12 <= ([w15,w16] * w14) mod n = (seed0 * x) mod n */
  bn.mov    w24, w15
  bn.mov    w25, w16
  bn.mov    w26, w14
  jal       x1, mod_mul_320x128
  bn.mov    w12, w19

  /* w13 <= ([w17,w18] * w14) mod n = (seed1 * x) mod n */
  bn.mov    w24, w17
  bn.mov    w25, w18
  bn.mov    w26, w14
  jal       x1, mod_mul_320x128
  bn.mov    w13, w19

  /* w12 <= (w12 + w13) mod n = ((seed0 + seed1) * x) mod n */
  bn.addm   w12, w12, w13

  /* Compare to 0.
     FG0.Z <= (w12 =? w31) = ((seed0 + seed1) mod n =? 0) */
  bn.cmp    w12, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, FG0, x0
  andi      x2, x2, 8

  /* Retry if x2 != 0. */
  bne       x2, x0, random_scalar_retry

  /* If we get here, then (seed0 + seed1) mod n is nonzero mod n; return. */

  ret

/**
 * Generate the secret key d from a random seed.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[out]  dmem[d0]:  first share of private key d
 * @param[out]  dmem[d1]:  second share of private key d
 *
 * clobbered registers: x2, x3, x20, w20, w21, w29
 * clobbered flag groups: FG0
 */
p256_generate_random_key:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Generate a random scalar in two 320-bit shares.
       w15, w16 <= d0
       w17, w18 <= d1 */
  jal  x1, p256_random_scalar

  /* Write first share to DMEM.
       dmem[d0] <= w15, w16 = d0 */
  la        x20, d0
  li        x2, 15
  bn.sid    x2, 0(x20++)
  li        x2, 16
  bn.sid    x2, 0(x20)

  /* Write second share to DMEM.
       dmem[d1] <= w15, w16 = d0 */
  la        x20, d1
  li        x2, 17
  bn.sid    x2, 0(x20++)
  li        x2, 18
  bn.sid    x2, 0(x20)

  ret

/**
 * Generate the secret scalar k from a random seed.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[out]  dmem[k0]:  first share of secret scalar k
 * @param[out]  dmem[k1]:  second share of secret scalar k
 *
 * clobbered registers: x2, x3, x20, w20, w21, w29
 * clobbered flag groups: FG0
 */
p256_generate_k:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Generate a random scalar in two 320-bit shares.
       w15, w16 <= k0
       w17, w18 <= k1 */
  jal  x1, p256_random_scalar

  /* Write first share to DMEM.
       dmem[k0] <= w15, w16 = k0 */
  la        x20, k0
  li        x2, 15
  bn.sid    x2, 0(x20++)
  li        x2, 16
  bn.sid    x2, 0(x20)

  /* Write second share to DMEM.
       dmem[k1] <= w15, w16 = k0 */
  la        x20, k1
  li        x2, 17
  bn.sid    x2, 0(x20++)
  li        x2, 18
  bn.sid    x2, 0(x20)

  ret

/**
 * Convert boolean shares to arithmetic ones using Goubin's algorithm.
 *
 * Returns x0, x1 such that (s0 ^ s1) = (x0 + x1) mod 2^321.
 *
 * The input consists of two 320-bit shares, s0 and s1. Bits at position 320
 * and above in the input shares will be ignored. We compute the result mod
 * 2^321 so that the high bit of x0 will reveal the carry modulo 2^320.
 *
 * We then use Goubin's boolean-to-arithmetic masking algorithm to switch from
 * this boolean masking scheme to an arithmetic one without ever unmasking the
 * seed. See Algorithm 1 here:
 * https://link.springer.com/content/pdf/10.1007/3-540-44709-1_2.pdf
 *
 * The algorithm is reproduced here for reference:
 *   Input:
 *     s0, s1: k-bit shares such that x = s0 ^ s1
 *     gamma: random k-bit number
 *   Output: x0, k-bit number such that x = (x0 + s1) mod 2^k
 *   Pseudocode:
 *     T := ((s0 ^ gamma) - gamma) mod 2^k
 *     T2 := T ^ s0
 *     G := gamma ^ s1
 *     A := ((s0 ^ G) - G) mod 2^k
 *     return x0 := (A ^ T2)
 *
 * The output x1 is always (s1 mod 2^320).
 *
 * This routine runs in constant time.
 *
 * We are aware that MSB of the intermediate values here may leak 1-bit of
 * secret seed. We observed this with formal masking analysis tool and FPGA
 * experiments. The algorithm runs with 64-bit excess randomness, so we don't
 * expect that to be possible to use that leakage and retrieve secret values.
 * We also verified that the leakage disappeared after running the routine on
 * 320-bit instead of 321-bit.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w21, w20]: s0, first share of seed (320 bits)
 * @param[in]  [w11, w10]: s1, second share of seed (320 bits)
 * @param[in]         w31: all-zero
 * @param[out] [w21, w20]: result x0 (321 bits)
 * @param[out] [w11, w10]: result x1 (320 bits)
 *
 * clobbered registers: w1 to w5, w20 to w23
 * clobbered flag groups: FG0
 */
boolean_to_arithmetic:
  /* Mask out excess bits from seed shares.
       [w21, w20] <= s0 mod 2^320
       [w11, w10] <= s1 mod 2^320 = x1 */
  bn.rshi   w21, w21, w31 >> 64
  bn.rshi   w21, w31, w21 >> 192
  bn.rshi   w31, w31, w31 >> 192 # dummy instruction to flush ALU datapath
  bn.rshi   w11, w11, w31 >> 64
  bn.rshi   w11, w31, w11 >> 192

  /* Fetch 321 bits of randomness from URND.
       [w2, w1] <= gamma */
  bn.wsrr   w1, 2
  bn.wsrr   w2, 2
  bn.rshi   w2, w31, w2 >> 191

  /* [w4, w3] <= [w21, w20] ^ [w2, w1] = s0 ^ gamma */
  bn.xor    w3, w20, w1
  bn.xor    w4, w21, w2

  /* Subtract gamma. This may result in bits above 2^321, but these will be
     stripped off in the next step.
       [w4, w3] <= [w4, w3] - [w2, w1] = ((s0 ^ gamma) - gamma) mod 2^512 */
  bn.sub    w3, w3, w1
  bn.subb   w4, w4, w2
  bn.sub    w31, w31, w31 # dummy instruction to clear flags

  /* Truncate subtraction result to 321 bits.
       [w4, w3] <= [w4, w3] mod 2^321 = T */
  bn.rshi   w4, w4, w31 >> 65
  bn.rshi   w4, w31, w4 >> 191

  /* [w4, w3] <= [w4, w3] ^ [w21, w20] = T2 */
  bn.xor    w3, w3, w20
  bn.xor    w4, w4, w21

  /* [w2, w1] <= [w2, w1] ^ [w11, w10] = gamma ^ s1 = G */
  bn.xor    w1, w1, w10
  bn.xor    w2, w2, w11

  /* [w21, w20] <= [w21, w20] ^ [w2, w1] = s0 ^ G */
  bn.xor    w20, w20, w1
  bn.xor    w21, w21, w2

  /* [w21, w20] <= [w21, w20] - [w2, w1] = ((s0 ^ G) - G) mod 2^512 */
  bn.sub    w20, w20, w1
  bn.subb   w21, w21, w2
  bn.sub    w31, w31, w31 # dummy instruction to clear flags

  /* [w21, w20] <= [w21, w20] mod 2^321 = A */
  bn.rshi   w21, w21, w31 >> 65
  bn.rshi   w21, w31, w21 >> 191

  /* apply fresh mask to w20 and w21 before xoring with w3 and w4 */
  bn.wsrr   w28, 1
  bn.wsrr   w29, 1
  bn.xor    w20, w28, w20
  bn.xor    w21, w29, w21

  /* [w21, w20] <= [w21, w20] ^ [w4, w3] = A ^ T2 = x0 */
  bn.xor    w20, w20, w3
  bn.xor    w21, w21, w4

  /* remove fresh mask */
  bn.xor    w20, w28, w20
  bn.xor    w21, w29, w21

  ret

/**
 * P-256 ECDSA secret key generation.
 *
 * Returns the secret key d in two 320-bit shares d0 and d1, such that:
 *    d = (d0 + d1) mod n
 * ...where n is the curve order.
 *
 * This implementation follows FIPS 186-4 section B.4.1, where we
 * generate d using N+64 random bits (320 bits in this case) as a seed. But
 * while FIPS computes d = (seed mod (n-1)) + 1 to ensure a nonzero key, we
 * instead just compute d = seed mod n. The caller MUST ensure that if this
 * routine is used, then other routines that use d (e.g. signing, public key
 * generation) are checking if d is 0.
 *
 * Most complexity in this routine comes from masking. The input seed is
 * provided in two 320-bit shares, seed0 and seed1, such that:
 *   seed = seed0 ^ seed1
 * Bits at position 320 and above in the input shares will be ignored.
 *
 * We then use Goubin's boolean-to-arithmetic masking algorithm to switch from
 * this boolean masking scheme to an arithmetic one without ever unmasking the
 * seed. See Algorithm 1 here:
 * https://link.springer.com/content/pdf/10.1007/3-540-44709-1_2.pdf
 *
 * For a Coq proof of the correctness of the basic computational logic here
 * see:
 *   https://gist.github.com/jadephilipoom/24f44c59cbe59327e2f753867564fa28#file-masked_reduce-v-L226
 *
 * The proof does not cover leakage properties; it mostly just shows that this
 * logic correctly computes (seed mod n) and the carry-handling works.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w21, w20]: seed0, first share of seed (320 bits)
 * @param[in]  [w11, w10]: seed1, second share of seed (320 bits)
 * @param[in]         w31: all-zero
 * @param[out] [w21, w20]: d0, first share of private key d (320 bits)
 * @param[out] [w11, w10]: d1, second share of private key d (320 bits)
 *
 * clobbered registers: x2, x3, w1 to w4, w20 to w29
 * clobbered flag groups: FG0
 */
p256_key_from_seed:
  /* Convert from a boolean to an arithmetic mask using Goubin's algorithm.
       [w21, w20] <= ((seed0 ^ seed1) - seed1) mod 2^321 = x0 */
  jal       x1, boolean_to_arithmetic

  /* At this point, we have arithmetic shares modulo 2^321:
       [w21, w20] : x0
       [w11, w10] : x1

     We know that x1=seed1, and seed and x1 are at most 320 bits. Therefore,
     the highest bit of x0 holds a carry bit modulo 2^320:
       x0 = (seed - x1) mod 2^321
       x0 = (seed - x1) mod 2^320 + (if (x1 <= seed) then 0 else 2^320)

     The carry bit then allows us to replace (mod 2^321) with a conditional
     statement:
       seed = (x0 mod 2^320) + x1 - (x0[320] << 320)

     Note that the carry bit is not very sensitive from a side channel
     perspective; x1 <= seed has some bias related to the highest bit of the
     seed, but since the seed is 64 bits larger than n, this single-bit noisy
     leakage should not be significant.

     From here, we want to convert to shares modulo (n * 2^64) -- these shares
     will be equivalent to the seed modulo n but still retain 64 bits of extra
     masking. We compute the new shares as follows:
       c = (x0[320] << 320) mod (n << 64)
       d0 = ((x0 mod 2^320) - c) mod (n << 64))
       d1 = x1 mod (n << 64)

       d = seed mod n = (d0 + d1) mod n
  */

  /* Load curve order n from DMEM.
       w29 <= dmem[p256_n] = n */
  li        x2, 29
  la        x3, p256_n
  bn.lid    x2, 0(x3)

  /* Compute (n << 64).
       [w29,w28] <= w29 << 64 = n << 64 */
  bn.rshi   w28, w29, w31 >> 192
  bn.rshi   w29, w31, w29 >> 192

  /* [w25,w24] <= (x1 - (n << 64)) mod 2^512 */
  bn.sub    w24, w10, w28
  bn.subb   w25, w11, w29

  /* Compute d1. Because 2^320 < 2 * (n << 64), a conditional subtraction is
     sufficient to reduce. Similarly to the carry bit, the conditional bit here
     is not very sensitive because the shares are large relative to n.
       [w11,w10] <= x1 mod (n << 64) = d1 */
  bn.sel    w10, w10, w24, FG0.C
  bn.sel    w11, w11, w25, FG0.C

  /* Isolate the carry bit and shift it back into position.
       w25 <= x0[320] << 64 */
  bn.rshi   w25, w31, w21 >> 64
  bn.rshi   w25, w25, w31 >> 192

  /* Clear the carry bit from the original result.
       [w21,w20] <= x0 mod 2^320 */
  bn.xor    w21, w21, w25

  /* Conditionally subtract (n << 64) to reduce.
       [w21,w20] <= (x0 mod 2^320) mod (n << 64) */
  bn.sub    w26, w20, w28
  bn.subb   w27, w21, w29
  bn.sel    w20, w20, w26, FG0.C
  bn.sel    w21, w21, w27, FG0.C

  /* Compute the correction factor.
       [w25,w24] <= (x[320] << 320) mod (n << 64) = c */
  bn.sub    w26, w31, w28
  bn.subb   w27, w25, w29
  bn.sel    w24, w31, w26, FG0.C
  bn.sel    w25, w25, w27, FG0.C

  /* Compute d0 with a modular subtraction. First we add (n << 64) to protect
     against underflow, then conditionally subtract it again if needed.
       [w21,w20] <= ([w21, w20] - [w25,w24]) mod (n << 64) = d1 */
  bn.add    w20, w20, w28
  bn.addc   w21, w21, w29
  bn.sub    w20, w20, w24
  bn.subb   w21, w21, w25
  bn.sub    w26, w20, w28
  bn.subb   w27, w21, w29
  bn.sel    w20, w20, w26, FG0.C
  bn.sel    w21, w21, w27, FG0.C

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

/* random scalar k (in two 320b shares) */
.balign 32
.weak k0
k0:
  .zero 64
.balign 32
.weak k1
k1:
  .zero 64

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

/* private key d (in two 320b shares) */
.balign 32
.weak d0
d0:
  .zero 64
.balign 32
.weak d1
d1:
  .zero 64

/* verification result x_r (aka x_1) */
.balign 32
.weak x_r
x_r:
  .zero 32
