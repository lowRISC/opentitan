/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl p256_shared_key

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
