/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * This library contains an implementation of the Ed25519 signature scheme
 * based on RFC 8032:
 *   https://datatracker.ietf.org/doc/html/rfc8032
 *
 * This implementation uses affine (x, y) coordinates at the interface but uses
 * the faster "extended twisted Edwards" coordinates internally. Procedures
 * that accept input in affine form are prefixed with affine_ and those that
 * accept input in extended form are prefixed with ext_.
 *
 * For verification, we slightly diverge from the RFC in terms of point
 * validation, because the RFC does not match most real-world code in certain
 * edge cases (and in fact, the RFC allows implementations to disagree with
 * each other on what constitutes a valid signature). A detailed walkthrough of
 * Ed25519 point validation issues and existing practice is here:
 *   https://hdevalence.ca/blog/2020-10-04-its-25519am
 *
 * Signatures constructed as requested by the RFC are unaffected by these
 * corner cases. However, maliciously constructed signatures can use these
 * small differences in validation criteria to cause problems for systems which
 * expect implementations to agree.
 *
 * In order to maximize compatibility and predictability, this implementation
 * adopts the ZIP215 set of validation criteria from Zcash, specified here:
 *   https://zips.z.cash/zip-0215
 *
 * Specifically, these rules are:
 *   - The scalar s in the signature must be canonical (< L). This matches the
 *     RFC but differs from some existing implementations such as the original
 *     "ref10".
 *   - The y coordinates of encoded points A and R are not required to be fully
 *     reduced modulo p (that is, it can be the case that y is in the
 *     range[2^255-19,2^255-1], which is not permitted by the RFC).
 *   - Encodings in which x=0 and the sign bit of x is 1 are permitted (the RFC
 *     disallows this).
 *   - Signatures must satisfy the "batched" equation [8][S]B = [8]R +
 *     [8][k]A', rather than the "unbatched" equation without the
 *     multiplications by 8 (the RFC allows implementers to check either, but
 *     they are not always equivalent for dishonestly constructed signatures).
 */

/**
 * Hardened values to encode success/failure of signature verification and
 * point decoding.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 21 -m 2 -n 32 \
 *     -s 1409634733 --language=c --avoid-zero
 *
 * Minimum Hamming distance: 21
 * Maximum Hamming distance: 21
 * Minimum Hamming weight: 21
 * Maximum Hamming weight: 22
 */
/* TODO: It would be nice to use these .equ declarations for success/failure
   magic values, but they cause errors in the assembler from the LI
   instructions.

.equ FAILURE,          0xeda2bfaf
.equ SUCCESS,          0xf77fe650
*/

/**
 * Constants for accessing flags.
 */
.equ CSR_FG0,          0x7c0

/**
 * Encode a point as described in RFC 8032, section 5.1.2.
 *
 * Returns enc = y | (lsb(x) << 255).
 *
 * The input point is in affine coordinates (x, y). From the RFC:
 *
 *   First, encode the y-coordinate as a little-endian string of 32 octets.
 *   The most significant bit of the final octet is always zero. To form the
 *   encoding of the point, copy the least significant bit of the x-coordinate
 *   to the most significant bit of the final octet.
 *
 * This encoding is sufficient for Ed25519 because each y corresponds to at
 * most two x coordinates, which have different least-significant bits.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w10: input x (x < p)
 * @param[in]  w11: input y (y < p)
 * @param[in]  w31: all-zero
 * @param[out] w11: enc, resulting encoded point
 *
 * clobbered registers: w10, w11
 * clobbered flag groups: FG0
 */
.globl affine_encode
affine_encode:
  /* w10 <= lsb(x) << 255 */
  bn.rshi  w10, w10, w31 >> 1
  /* w11 <= w11 | w10 = y | (lsb(x) << 255) = enc */
  bn.or    w11, w11, w10
  ret

/**
 * Decode a point (see RFC 8032, section 5.1.3).
 *
 * Returns (x, y), the decoded point in affine coordinates.
 *
 * Broadly, point decoding involves:
 *   - Extracting the y value and lsb(x)
 *   - Solving the curve equation to get two candidates for x.
 *   - Use lsb(x) to select the correct candidate.
 *
 * This implementation, in accordance with ZIP215 validation criteria, will
 * accept non-canonical values of y in the range [p,2^255). However, the output
 * y value will be fully reduced modulo p.
 *
 * Since the inputs to this routine are all public values, there's no need to
 * make it constant-time.
 *
 * This routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w11: encoded point: y | (lsb(x) << 255)
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  w30: constant, w30 = d = (-121665/121666) mod p
 * @param[in]  w31: all-zero
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[out] x20: SUCCESS or FAILURE code
 * @param[out] w10: output x (x < p) (only valid if x20=SUCCESS)
 * @param[out] w11: output y (y < p) (only valid if x20=SUCCESS)
 *
 * clobbered registers: w10, w11, w14 to w18, w20 to w28
 * clobbered flag groups: FG0
 */
.globl affine_decode_var
affine_decode_var:
  /* Extract lsb(x) from the encoded point.
       w24 <= w11 >> 255 = lsb(x) */
  bn.rshi  w24, w31, w11 >> 255

  /* Extract y from the encoded point.
       w11 <= w11[254:0] = y */
  bn.rshi  w11, w11, w31 >> 255
  bn.rshi  w11, w31, w11 >> 1

  /* Defensively reduce y modulo p in case y is non-canonical.
       w11 <= (w11 + 0) mod p = w11 mod p */
  bn.addm  w11, w11, w31

  /* Solve the curve equation to get a candidate root. From RFC 8032,
     section 5.1.3, step 2:

       To recover the x-coordinate, the curve equation implies
       x^2 = (y^2 - 1) / (d y^2 + 1) (mod p).  The denominator is always
       non-zero mod p.  Let u = y^2 - 1 and v = d y^2 + 1.  To compute
       the square root of (u/v), the first step is to compute the
       candidate root r = (u/v)^((p+3)/8).  This can be done with the
       following trick, using a single modular powering for both the
       inversion of v and the square root:

                          (p+3)/8      3        (p-5)/8
                 r = (u/v)        = u v  (u v^7)         (mod p)

     Note: the RFC uses the name "x" for the candidate root, but we use "r"
     instead to distinguish the candidate root from the final computed x
     coordinate.

     The RFC doesn't give the mathematical background for why this formula
     works, but here's some quick intuition:
       - Euler's criterion states that if n has a square root modulo p, then
         n^((p-1) / 2) mod p = 1 (and if there's no square root, it's p-1).
       - Fermat's Little Theorem states that the inverse of n modulo p (where p
         is prime and 0 < n < p) is n^(p-1).
       - The "candidate root" r is such that r^4 = (u/v)^2 if (u/v) is square
         mod p, or -(u/v)^2 if (u/v) is nonsquare. This follows from Euler's
         criterion, because
           r^4 = (u/v)^((p+3)/2) = (u/v)^((p-1)/2) * (u/v)^2
       - If the provided point is valid, then (u/v) = x^2 and (u/v) must be
         square modulo p.
   */

   /* Store the constant 1, which will be used to compute u and v.
        w25 <= 1 */
   bn.addi   w25, w31, 1

   /* Compute u and v. */

   /* w22 <= (w11^2) mod p = y^2 mod p */
   bn.mov   w22, w11
   jal      x1, fe_square
   /* w26 <= (w22 - w25) mod p <= (y^2 - 1) mod p = u */
   bn.subm  w26, w22, w25
   /* w22 <= (w22 * w30) mod p = (y^2 * d) mod p */
   bn.mov   w23, w30
   jal      x1, fe_mul
   /* w25 <= (w22 + w25) mod p = (y^2 * d + 1) mod p = v */
   bn.addm  w25, w22, w25

   /* Compute the candidate root r = (u*(v^3))((u*(v^7))^((p-5)/8)) mod p. */

   /* w27 <= (w26 * w25) mod p = (u * v) mod p */
   bn.mov   w22, w26
   bn.mov   w23, w25
   jal      x1, fe_mul
   bn.mov   w27, w22
   /* w28 <= (w25^2) mod p = (v^2) mod p */
   bn.mov   w22, w25
   jal      x1, fe_square
   bn.mov   w28, w22
   /* w27 <= (w27 * w28) mod p = (u * v^3) mod p */
   bn.mov   w22, w27
   bn.mov   w23, w28
   jal      x1, fe_mul
   bn.mov   w27, w22
   /* w22 <= (w28^2) mod p = (v^4) mod p */
   bn.mov   w22, w28
   jal      x1, fe_square
   /* w22 <= (w22 * w27) mod p = (u * v^7) mod p */
   bn.mov   w23, w27
   jal      x1, fe_mul
   /* w22 <= (w22^((p-5)/8)) mod p = (u * v^7)^((p-5)/8) mod p */
   bn.mov   w16, w22
   jal      x1, fe_pow_2252m3
   /* w22 <= (w22 * w27) mod p = r */
   bn.mov   w23, w27
   jal      x1, fe_mul

  /* Use the candidate root to derive two possible square roots of x^2. From
     RFC 8032, section 5.1.3, step 3 (with the candidate root again shown as r
     instead of x to avoid confusion):

       Again, there are three cases:

       1.  If v r^2 = u (mod p), r is a square root.

       2.  If v r^2 = -u (mod p), set r <-- r * 2^((p-1)/4), which is a
           square root.

       3.  Otherwise, no square root exists for modulo p, and decoding
           fails.

     Again the RFC doesn't really explain the mathematics here. Recall from the
     last step that:
        (u/v) = x^2       if u and v represent a valid y coordinate
        r^4   = (u/v)^2   if (u/v) is square mod p
        r^4   = - (u/v)^2 if (u/v) is nonsquare mod p

     If (u/v) is nonsquare mod p, then it cannot be that (u/v) = x^2, so the
     point cannot be valid. The case-analysis from the RFC refines the
     candidate root so that we reject the nonsquare case, and obtain r such
     that r^2 = x^2.

     The three cases represented in the RFC represent the three possible values
     of r^2 in this situation:
       1. r^2 == (u/v), in which case r^2 = x^2 and we're done.
       2. r^2 == - (u/v), in which case (r * sqrt(-1))^2 = x^2. Since we're
          working modulo p, sqrt(-1) is a real number; 2^((p-1)/4) is indeed a
          valid square root of -1 mod p.
       3. Otherwise, (u/v) is nonsquare and we can reject the point.
  */

  /* Compute (r^2 * v) mod p. */

  /* Save the original r value for later.
        w27 <= w22 = r */
  bn.mov   w27, w22

  /* w22 <= (w22^2) mod p = (r^2) mod p */
  jal      x1, fe_square
  /* w22 <= (w22 * w25) mod p = (r^2 * v) mod p */
  bn.mov   w23, w25
  jal      x1, fe_mul

  /* Check for case 1: (r^2 * v) mod p == u. */

  /* x3 <= 8 */
  addi     x3, x0, 8

  /* FG0.Z <= (w22 - w26 == 0) = ((r^2 * v) mod p == u) */
  bn.cmp   w22, w26
  /* x2 <= FG0[3] = FG0.Z = ((r^2 * v) mod p == u) */
  csrrs    x2, CSR_FG0, x0
  and      x2, x2, x3

  /* Go to step 3, case 1 if we are in case 1. */
  beq      x2, x3, decode_step3_case1

  /* Check for case 2: (r^2 * v) mod p == (- u) mod p */

  /* w28 <= (w31 - w26) mod p = (0 - u) mod p */
  bn.subm  w28, w31, w26

  /* FG0.Z <= (w22 - w28 == 0) = ((r^2 * v) mod p == (-u) mod p) */
  bn.cmp   w22, w28
  /* x2 <= FG0[3] = FG0.Z = ((r^2 * v) mod p == (-u) mod p) */
  csrrs    x2, CSR_FG0, x0
  and      x2, x2, x3

  /* Go to step 3, case 2 if we are in case 2. */
  beq      x2, x3, decode_step3_case2

  /* If we get here, then r^2 was not equal to either (u/v) or - (u/v), so we
     are in case 3, (u/v) is nonsquare mod p, and point decoding fails. */
  li       x20, 0xeda2bfaf
  bn.mov   w10, w31
  bn.mov   w11, w31
  ret

  decode_step3_case2:
  /* Multiply r by sqrt(-1) = 2^((p-1)/4). */

  /* w23 <= dmem[ed25519_sqrt_m1] = sqrt(-1) mod p */
  la       x2, ed25519_sqrt_m1
  li       x3, 23
  bn.lid   x3, 0(x2)

  /* w27 <= (w27 * w23) mod p = (r * sqrt(-1)) mod p */
  bn.mov   w22, w27
  jal      x1, fe_mul
  bn.mov   w27, w22

  /* From here, r^2 = x^2 and we can proceed with the same steps as case 1. */

  decode_step3_case1:
  /* Once we're here, we know that r^2 = x^2, and therefore r is either x or
     -x. Following RFC 8032, section 5.1.3, step 4, we set the resulting
     point's x coordinate to r if lsb(x) from the encoded point matches lsb(r),
     and set x to (-r) mod p otherwise.

     Because we are following the ZIP15 validation criteria instead of the RFC,
     we allow the case where x=0 but the encoded lsb(x)=1, so that check is
     skipped here. In this case, we will decode x as (-0) mod p = 0.

     Code here expects:
       w27: r such that r^2 = x^2 (mod p).
       w31: all-zero
  */

  /* Compute (-r) mod p.
       w10 <= (w31 - w27) mod p = (-r) mod p */
  bn.subm  w10, w31, w27

  /* Set FG.L to be 1 iff the LSBs of r and x are mismatched.
       FG0.L <= lsb(w24 ^ w27) = lsb(lsb(x) ^ r) = lsb(x) ^ lsb(r) = (lsb(x) != lsb(r)) */
  bn.xor   w24, w27, w24

  /* If the LSBs are mismatched, select (-r) mod p; otherwise select r.
       w10 <= FG0.L ? w10 : w27
                = if (lsb(x) != lsb(r)) then (-r) mod p else r */
  bn.sel   w10, w10, w27, FG0.L

  /* TODO: add an extra check that the curve equation is satisfied to protect
     against glitching? */

  /* Exit point decoding with SUCCESS. */
  li       x20, 0xf77fe650

  ret

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

.data

/* Square root of -1 modulo p=2^255-19.
   Equal to (2^((p-1)/4)) mod p. */
.balign 32
ed25519_sqrt_m1:
  .word 0x4a0ea0b0
  .word 0xc4ee1b27
  .word 0xad2fe478
  .word 0x2f431806
  .word 0x3dfbd7a7
  .word 0x2b4d0099
  .word 0x4fc1df0b
  .word 0x2b832480
