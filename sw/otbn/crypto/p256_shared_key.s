/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl p256_shared_key

.text

/**
 * Externally callable wrapper for P-256 scalar point multiplication.
 *
 * Returns x0, x1 such that x0 ^ x1 = x-coordinate of (d * P) and y0, y1 such
 * that y0 ^ y1 = y-coordinate of (d * P).
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
 * @param[out]     dmem[ecdh_x0]: x0, first share of x-coordinate in dmem
 * @param[out]     dmem[ecdh_x1]: x1, second share of x-coordinate in dmem
 * @param[out]     dmem[ecdh_y0]: y0, first share of y-coordinate in dmem
 * @param[out]     dmem[ecdh_y1]: y1, second share of y-coordinate in dmem
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
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
   1. Generate random masks m_x and m_y
   2. Subtract masks from projective x and y coordinates
      (x, y, z) -> ((x - m_x) mod p,
                    (y - m_y) mod p,
                     z)
   3. Convert masked curve point back to affine
      form.
   4. Multiply masks with z^-1 for use in
      affine space. */

  /* Fetch fresh random numbers as masks.
       w2 <= URND() = m_x
       w3 <= URND() = m_y */
  bn.wsrr   w2, URND
  bn.xor    w31, w31, w31 /* dummy */
  bn.wsrr   w3, URND

  /* Subtract random masks from x and y coordinates of
     projective point.
     The subtraction has to be done within the underlying
     finite field -> mod p.
     w8 = (w8 - w2) mod p
     w9 = (w9 - w3) mod p */
  bn.subm   w8, w8, w2
  bn.xor    w31, w31, w31 /* dummy */
  bn.subm   w9, w9, w3

  /* Convert masked result back to affine coordinates.
     R = (x_a, y_a) = (w11, w12) */
  jal       x1, proj_to_affine

  /* Store result (masked affine coordinates) in DMEM.
     dmem[ecdh_x0] <= x_a = w11
     dmem[ecdh_y0] <= y_a = w12 */
  li        x2, 11
  la        x3, ecdh_x0
  bn.sid    x2++, 0(x3)
  la        x3, ecdh_y0
  bn.sid    x2, 0(x3)

  /* Get modular inverse z^-1 of projective z coordinate
     and multiply the random masks with z^-1 to
     also convert them into affine space. */

  /* Move z^-1 and y coordinate mask to mul_modp input WDRs.
     z^-1 is still stored in w14 from previous
     proj_to_affine call.
     w25 <= w14 = z^-1
     w24 <= w3 = m_y */
  bn.mov    w25, w14
  bn.mov    w24, w3

  /* Compute modular multiplication of m_y and z^-1.
     w19 = w24 * w25 mod p = m_y * z^-1 mod p = y1 */
  jal       x1, mul_modp

  /* Store "affine" y mask to DMEM.
     dmem[ecdh_y1] <= w19 = y1 */
  li        x2, 19
  la        x3, ecdh_y1
  bn.sid    x2, 0(x3)

  /* Move z^-1 and x coordinate mask to mul_modp input WDRs.
     w25 <= w14 = z^-1
     w24 <= w2 = m_x */
  bn.mov    w25, w14
  bn.mov    w24, w2

  /* Compute modular multiplication of m_x and z^-1.
     w19 = w24 * w25 mod p = m_x * z^-1 mod p = x1 */
  jal       x1, mul_modp

  /* Store "affine" x mask to DMEM.
     dmem[ecdh_x1] <= w19 = x1 */
  li        x2, 19
  la        x3, ecdh_x1
  bn.sid    x2, 0(x3)

  /* Arithmetic-to-boolean conversion of the x-coordinate.
     w11 (x_a) and w19 (x1) are still intact from above.
       w20 <= x ^ x1 = x0 */
  jal       x1, arithmetic_to_boolean_mod

  /* dmem[ecdh_x0] <= w20 = x0 */
  li        x2, 20
  la        x3, ecdh_x0
  bn.sid    x2, 0(x3)

  /* Load the masked y-coordinate and its mask for the
     arithmetic-to-boolean conversion.
       w11 <= dmem[ecdh_y0] = y_a
       w19 <= dmem[ecdh_y1] = y1 */
  li        x2, 11
  la        x3, ecdh_y0
  bn.lid    x2, 0(x3)
  li        x2, 19
  la        x3, ecdh_y1
  bn.lid    x2, 0(x3)

  /* Arithmetic-to-boolean conversion of the y-coordinate.
       w20 <= y ^ y1 = y0 */
  jal       x1, arithmetic_to_boolean_mod

  /* dmem[ecdh_y0] <= w20 = y0 */
  li        x2, 20
  la        x3, ecdh_y0
  bn.sid    x2, 0(x3)

  ret

.section .data

/* ECDH shared key output: boolean shares of the x- and y-coordinates. */
.balign 32
.weak ecdh_x0
ecdh_x0:
  .zero 32
.balign 32
.weak ecdh_x1
ecdh_x1:
  .zero 32
.balign 32
.weak ecdh_y0
ecdh_y0:
  .zero 32
.balign 32
.weak ecdh_y1
ecdh_y1:
  .zero 32
