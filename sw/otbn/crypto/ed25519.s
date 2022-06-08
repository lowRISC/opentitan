/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * This library contains an implementation of the Ed25519
 * signature scheme following RFC 8032:
 *   https://datatracker.ietf.org/doc/html/rfc8032
 */

/**
 * Add two points in extended twisted Edwards coordinates.
 *
 * Returns (X3, Y3, Z3, T3) = (X1, Y1, Z1, T1) + (X2, Y2, Z2, T2)
 *
 * Overwrites the first operand (X1, Y1, Z1, T1) with the result. The second
 * operand is not modified.
 *
 * This implementation closely follows RFC 8032, section 5.1.4:
 *   https://datatracker.ietf.org/doc/html/rfc8032#section-5.1.4
 *
 * A point is represented as 4 integers (X, Y, Z, T) in the field modulo
 * p=2^255-19. As per the RFC, we can compute addition on any two points (X1,
 * Y1, Z1, T1) and (X2, Y2, Z2, T2) with the formula:
 *
 *   A = (Y1-X1)*(Y2-X2)
 *   B = (Y1+X1)*(Y2+X2)
 *   C = T1*2*d*T2
 *   D = Z1*2*Z2
 *   E = B-A
 *   F = D-C
 *   G = D+C
 *   H = B+A
 *   X3 = E*F
 *   Y3 = G*H
 *   T3 = E*H
 *   Z3 = F*G
 *
 * In the formula above, all arithmetic (+, *, -) is modulo p=2^255-19, and the
 * constant d is as described in section 5.1:
 *   https://datatracker.ietf.org/doc/html/rfc8032#section-5.1
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w19: constant, 19
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[in]  w29: constant, (2*d) mod p, d = (-121665/121666) mod p
 * @param[in]  w30: constant, 38
 * @param[in]  w31: all-zero
 * @param[in,out] w10: input X1 (X1 < p), output X3
 * @param[in,out] w11: input Y1 (Y1 < p), output Y3
 * @param[in,out] w12: input Z1 (Z1 < p), output Z3
 * @param[in,out] w13: input T1 (T1 < p), output T3
 * @param[in]     w14: input X2 (X2 < p)
 * @param[in]     w15: input Y2 (Y2 < p)
 * @param[in]     w16: input Z2 (Z2 < p)
 * @param[in]     w17: input T2 (T2 < p)
 *
 * clobbered registers: w10 to w13, w18, w20 to w23, w24 to w27
 * clobbered flag groups: FG0
 */
.globl ext_add
ext_add:
  /* Compute A = (Y1 - X1) * (Y2 - X2). */

  /* w22 <= Y1 - X1 */
  bn.subm  w22, w11, w10
  /* w23 <= Y2 - X2 */
  bn.subm  w23, w15, w14
  /* w22 <= w22 * w23 = A */
  jal      x1, fe_mul
  /* w24 <= w22 = A */
  bn.mov   w24, w22

  /* Compute B = (Y1 + X1) * (Y2 + X2). */

  /* w22 <= Y1 + X1 */
  bn.addm  w22, w11, w10
  /* w23 <= Y2 + X2 */
  bn.addm  w23, w15, w14
  /* w22 <= w22 * w23 = B */
  jal      x1, fe_mul
  /* w25 <= w22 = B */
  bn.mov   w25, w22

  /* Compute C = T1*2*d*T2. */

  /* w22 <= w13 = T1 */
  bn.mov   w22, w13
  /* w23 <= w29 <= 2*d */
  bn.mov   w23, w29
  /* w22 <= w22 * w23 = T1*2*d */
  jal      x1, fe_mul
  /* w23 <= w17 = T2 */
  bn.mov   w23, w17
  /* w22 <= w22 * w23 = C */
  jal      x1, fe_mul
  /* w26 <= w22 = C */
  bn.mov   w26, w22

  /* Compute D = Z1*2*Z2. */

  /* w22 <= w12 = Z1 */
  bn.mov   w22, w12
  /* w23 <= 2 */
  bn.addi  w23, w31, 2
  /* w22 <= w22 * w23 = Z1*2 */
  jal      x1, fe_mul
  /* w23 <= w16 = Z2 */
  bn.mov   w23, w16
  /* w22 <= w22 * w23 = D */
  jal      x1, fe_mul
  /* w27 <= w22 = D */
  bn.mov   w27, w22

  /* Compute X3 = (B - A) * (D - C). */

  /* w22 <= w25 - w24 = B - A */
  bn.subm  w22, w25, w24
  /* w23 <= w27 - w26 = D - C */
  bn.subm  w23, w27, w26
  /* w22 <= w22 * w23 = X3 */
  jal      x1, fe_mul
  /* w10 <= w22 = X3 */
  bn.mov   w10, w22

  /* Compute Z3 = (D + C) * (D - C). */

  /* w22 <= w27 + w26 = D + C */
  bn.addm  w22, w27, w26
  /* w22 <= w22 * w23 = Z3 */
  jal      x1, fe_mul
  /* w12 <= w22 = Z3 */
  bn.mov   w12, w22

  /* Compute Y3 = (D + C) * (B + A). */

  /* w22 <= w27 + w26 = D + C */
  bn.addm  w22, w27, w26
  /* w23 <= w25 + w24 = B + A */
  bn.addm  w23, w25, w24
  /* w22 <= w22 * w23 = Y3 */
  jal      x1, fe_mul
  /* w11 <= w22 = Y3 */
  bn.mov   w11, w22

  /* Compute T3 = (B - A) * (B + A). */

  /* w22 <= w25 - w24 = B - A */
  bn.subm  w22, w25, w24
  /* w22 <= w22 * w23 = T3 */
  jal      x1, fe_mul
  /* w13 <= w22 = T3 */
  bn.mov   w13, w22

  ret

/**
 * Raise a coordinate field element (modulo p) to the power of ((p-5) / 8).
 *
 * Returns c = a^(2^252-3) mod p.
 *
 * This calculation is used during point decoding (see RFC 8032, section
 * 5.1.3):
 *
 * Note: Most of this chain is the same as fe_inv. To save code size, it would
 * be possible to have both fe_inv and this routine share some code. For some
 * performance gains, it may well be possible to find a more efficient chain.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  w16: a, first operand, a < p
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[in]  w31: all-zero
 * @param[out] w22: c, result
 *
 * clobbered registers: w14, w15, w17, w18, w20 to w23
 * clobbered flag groups: FG0
 */
fe_pow_2252m3:
  /* w22 <= w16^2 = a^2 */
  bn.mov  w22, w16
  jal     x1, fe_square
  /* w23 <= w22 = a^2 */
  bn.mov  w23, w22

  /* w22 <= w22^4 = a^8 */
  jal     x1, fe_square
  jal     x1, fe_square

  /* w22 <= w22 * w23 = a^10 */
  jal     x1, fe_mul
  /* w15 <= w22 = a^10 */
  bn.mov  w15, w22

  /* w22 <= w22 * w16 = a^11 */
  bn.mov  w23, w16
  jal     x1, fe_mul
  /* w14 <= w22 <= a^11 */
  bn.mov  w14, w22

  /* w22 <= w15^2 = a^20 */
  bn.mov  w22, w15
  jal     x1, fe_square

  /* w22 <= w22 * w14 = a^31 = a^(2^5 - 1) */
  bn.mov  w23, w14
  jal     x1, fe_mul
  /* w23 <= w22 = a^(2^5 - 1) */
  bn.mov  w23, w22

  /* w22 <= w22^(2^5) = a^(2^10-2^5) */
  loopi   5,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^10-1) */
  jal     x1, fe_mul
  /* w23 <= w22 <= a^(2^10-1) */
  bn.mov  w23, w22
  /* w15 <= w22 <= a^(2^10-1) */
  bn.mov  w15, w22

  /* w22 <= w22^(2^10) = a^(2^20-2^10) */
  loopi   10,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^20-1) */
  jal     x1, fe_mul
  /* w23 <= w22 <= a^(2^20-1) */
  bn.mov  w23, w22

  /* w22 <= w22^(2^20) = a^(2^40-2^20) */
  loopi   20,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^40-1) */
  jal     x1, fe_mul

  /* w22 <= w22^(2^10) = a^(2^50-2^10) */
  loopi   10,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w15 = a^(2^50-1) */
  bn.mov  w23, w15
  jal     x1, fe_mul
  /* w23 <= w22 <= a^(2^50-1) */
  bn.mov  w23, w22
  /* w15 <= w22 <= a^(2^50-1) */
  bn.mov  w15, w22

  /* w22 <= w22^(2^50) = a^(2^100-2^50) */
  loopi   50,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^100-1) */
  jal     x1, fe_mul
  /* w23 <= w22 <= a^(2^100-1) */
  bn.mov  w23, w22

  /* w22 <= w22^(2^100) = a^(2^200-2^100) */
  loopi   100,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^200-1) */
  jal     x1, fe_mul

  /* w22 <= w22^(2^50) = a^(2^250-2^50) */
  loopi   50,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w15 = a^(2^250-1) */
  bn.mov  w23, w15
  jal     x1, fe_mul

  /* w22 <= w22^4 = a^(2^252-2^2) */
  jal     x1, fe_square
  jal     x1, fe_square

  /* w22 <= w22 * w16 = a^(2^252 - 2^2 + 1) = a^(2^252 - 3) */
  bn.mov  w23, w16
  jal     x1, fe_mul

  ret
