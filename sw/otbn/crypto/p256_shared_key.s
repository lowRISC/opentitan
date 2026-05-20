/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl p256_shared_key

/* Exposed only for testing or SCA purposes. */
.globl arithmetic_to_boolean_mod

.text

/**
 * Externally callable wrapper for P-256 scalar point multiplication.
 *
 * Returns x0, x1 such that x0 ^ x1 = x-coordinate of (d * P).
 *
 * This routine is specialized for ECDH shared key generation and includes an
 * arithmetic-to-boolean masking conversion.
 *
 * This routine assumes that the scalar d is provided in two arithmetic shares,
 * d0 and d1, where d = (d0 + d1) mod n.
 *
 * This routine runs in constant time.
 *
 * @param[in]      dmem[d0]:  first share of scalar d (320 bits)
 * @param[in]      dmem[d1]:  second share of scalar d (320 bits)
 * @param[in]      dmem[x]:   affine x-coordinate in dmem
 * @param[in]      dmem[y]:   affine y-coordinate in dmem
 * @param[out]     dmem[x]:   x0, first share of x-coordinate in dmem
 * @param[out]     dmem[y]:   x1, second share of x-coordinate in dmem
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x16, x17, x21, x22, w0 to w25
 * clobbered flag groups: FG0
 */
p256_shared_key:
  /* Init all-zero register. */
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

  /* Reblind the secret key before running the scalar multiplication. */
  jal       x1, p256_masked_scalar_reblind

  /* Call internal scalar multiplication routine.
     Returns point in projective coordinates.
     R = (x, y, z) = (w8, w9, w10) <= d*P = ([w0,w1] + [w2,w3])*P */
  la        x21, x
  la        x22, y
  jal       x1, scalar_mult_int

  /* store result (affine coordinates) in dmem
     dmem[x] <= x = w8
     dmem[y] <= y = w9
     dmem[z] <= z = w10 */
  li        x2, 8
  la        x21, x
  bn.sid    x2++, 0(x21)
  la        x22, y
  bn.sid    x2++, 0(x22)
  la        x21, z
  bn.sid    x2, 0(x21)

  /* Compute both sides of the Weierstrauss equation.
       w18 <= (x^3 + ax + b) mod p
       w19 <= (y^2) mod p */
  jal      x1, p256_isoncurve_proj

  /* Compare the two sides of the equation to check if the result
     is a valid point as an FI countermeasure.
     The check fails if both sides are not equal.
     FG0.Z <= (y^2) mod p == (x^2 + ax + b) mod p */
  bn.cmp   w18, w19
  jal      x1, trigger_fault_if_fg0_z

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
  bn.wsrr   w2, URND

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

  /* Move z^-1 and x coordinate mask to mul_modp input WDRs.
     z^-1 is still stored in w14 from previous
     proj_to_affine call.
     w25 <= w14 = z^-1
     w24 <= w2 = m_x */
  bn.mov    w25, w14
  bn.mov    w24, w2

  /* Compute modular multiplication of m_x and z^-1.
     w19 = w24 * w25 mod p = m_x * z^-1 mod p = x1 */
  jal       x1, mul_modp

  /* Store "affine" mask to DMEM. Use the y-coordinate
     to save memory (not needed afterwards)
     dmem[y] <= w19 = x1 */
  li        x2, 19
  bn.sid    x2, 0(x22)

  /* Arithmetic-to-boolean conversion.
       w20 <= x ^ x1 = x0 */
  jal       x1, arithmetic_to_boolean_mod

  /* dmem[x] <= w20 = x0 */
  li        x3, 20
  la        x4, x
  bn.sid    x3, 0(x4)

  ret

/**
 * Converts arithmetic shares mod p to boolean shares.
 *
 * Calls the 257-bit A2B function twice, first using unmodified 256-bit shares
 * in reduced form, and then using modified 257-bit shares in unreduced form.
 *
 * It then checks if the MSB (carry bit) is true or false, to decide
 * which of the two A2B results is used. This detects and handles an
 * underflow during the subtraction of arithmetic masking.
 *
 * The logic behind the carry bit handling is as follows:
 * If x >= r, then  A = (x - r) mod p = x - r exactly.
 * So when we add 2^257 - p and then add A and r, we get
 * (2^257 - p + x - r + r) mod 2^257 = 2^257 - p + x.
 * In this case, the high bit is always true since p - x <= p < 2^256,
 * so we choose the A2B conversion without the 2^257 - p added.
 * On the other hand, if x < r, then A = (x - r) mod p = x - r + p.
 * When we add 2^257 - p and then add A and r, we get
 * (2^257 - p + x - r + p + r) mod 2^257 = (2^257 + x) mod 2^257 = x.
 * In this case, the high bit is always false since x < p < 2^256, so we
 * choose this second A2B conversion.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w31: all-zero wide data register
 * @param[in]  w19: mask r
 * @param[in]  w11: arithmetically masked value A, such that x = A + r
 * @param[out] w20: boolean masked value x', such that x = x' ^ r
 *
 * clobbered registers: w1 to w6, w11, w12, w18, w20 to w27, and w29
 * clobbered flag groups: FG0
 */
arithmetic_to_boolean_mod:
  /* First step: calculate A2B from reduced values. */

  /* Save inputs for second A2B execution. Also, expand inputs r and A (w19
     and w11) to 257-bit values [w19,w18] and [w12,w11] and prepare input for
     257-bit A2B function.

     N.B. Accesses to w19 and w11 have been intentionally made non-sequential to
     avoid transient side channel leakage.

     w24 <= w19 = r
     w25 <= w11 = A
     w18 <= w19
     w19 <= w31
     w11 <= w11 -> obsolete
     w12 <= w31 */
  bn.mov    w24, w19
  bn.mov    w18, w19
  bn.mov    w12, w31
  bn.mov    w19, w31
  bn.mov    w25, w11

  /* Call 257-bit A2B function.
     [w21,w20] <= x' */
  jal       x1, arithmetic_to_boolean

  /* Save intermediate result of reduced inputs.
     w26 <= w20 = x' (lower part)
     w27 <= w21 = x' (upper part) */
  bn.mov    w26, w20
  bn.mov    w27, w21

  /* Second step: calculate A2B from unreduced values. */

  /* Restore and expand inputs r and A (w19 and w11) to 257-bit
     values [w19,w18] and [w12,w11] and prepare input for
     257-bit A2B function.
     w18 <= w24
     w19 <= w31
     w11 <= w25
     w12 <= w31 */
  bn.mov    w18, w24
  bn.mov    w19, w31
  bn.mov    w11, w25
  bn.mov    w12, w31

  /* Get field modulus p.
     w29 <= MOD() */
  bn.wsrr   w29, MOD

  /* Convert input A ([w12,w11]) to an unreduced value
     in the 2^257 domain. For this add (2^257 - p) to A.
     [w12,w11] <= [w12,w11] + 2^257 - w29 = A + 2^257 - p
     w12 <= w12 + 0x2 = A + 2^257
            -> equal to addition of 2^257
               (w11 doesn't need to be touched)
     [w12,w11] <= [w12,w11] - w29 = (A + 2^257) - p

     N.B. The dummy instruction below is to clear the flags from performing
     the subtractions, as their state is dependent on w11 and w12, which is
     a known constant offset (2^257 - p) from the secret share A. */
  bn.addi   w12, w12, 0x2
  bn.sub    w11, w11, w29
  bn.subb   w12, w12, w31
  bn.sub    w22, w22, w22  /* dummy instruction to clear flags */

  /* Call 257-bit A2B function.
     [w21,w20] <= x' */
  jal       x1, arithmetic_to_boolean

  /* Restore initial mask input of w19 for consistency
     in calling functions.
     w19 <= w24 */
  bn.mov    w19, w24

  /* Move reduced A2B computation result to a separate register to prevent
     below bn.sel leaking FG0.Z.

     N.B. The dummy instruction below serves to make the accesses to w19
     (containing r) and w20 (containing the lower word of x') non-sequential. */
  bn.mov    w31, w31  /* dummy instruction to avoid transient leakage */
  bn.mov    w25, w20

  /* Check MSb (carry bit) of second A2B result for true or false. */
  bn.cmp    w21, w31  /* w21 can only be 0x1 or 0x0 */

  /* Return the unreduced A2B computation (second result),
     if zero flag is set, otherwise return the reduced
     A2B computation (first result). */
  bn.sel    w20, w25, w26, FG0.Z
  bn.sel    w31, w31, w31, FG0.Z  /* dummy instruction to clear flags */

  ret
