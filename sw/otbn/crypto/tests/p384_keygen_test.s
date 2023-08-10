/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 key/scalar generation
 *
 * Performs generation of a P-384 random secret key and scalar.
 *
 * This test does not test if the randomness of the generated values is
 * properly distributed or if the entropy is large enough etc.
 * It only checks if a few generated values are distinct and if the
 * associated shares don't add up to zero (mod n).
 *
 * Actual randomness testing has to be done vial statistical analysis
 * of generated values, but this is not possible for simulator based
 * automated testing.
 */

.section .text.start

p384_keygen_test:

  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* set dmem pointer to point to 1st scalar share k0 */
  la        x2, k0
  la        x3, dptr_k0
  sw        x2, 0(x3)

  /* set dmem pointer to point to 2nd scalar share k1 */
  la        x2, k1
  la        x3, dptr_k1
  sw        x2, 0(x3)

  /* set dmem pointer to point to 1st scalar share d0 (private key) */
  la        x2, d0
  la        x3, dptr_d0
  sw        x2, 0(x3)

  /* set dmem pointer to point to 2nd scalar share d1 (private key) */
  la        x2, d1
  la        x3, dptr_d1
  sw        x2, 0(x3)

  /* generate 4 random 448-bit values and write them to d0, d1, k0, k1 */
  jal       x1, p384_generate_random_key
  jal       x1, p384_generate_k

  /* load generated values into WDRs for range/distinctiveness check */
  li        x2, 4

  /* [w5,w4] <= d0 */
  la        x3, dptr_d0
  lw        x4, 0(x3)
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* [w7,w6] <= d1 */
  la        x3, dptr_d1
  lw        x4, 0(x3)
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* [w9,w8] <= k0 */
  la        x3, dptr_k0
  lw        x4, 0(x3)
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* [w11,w10] <= k1 */
  la        x3, dptr_k1
  lw        x4, 0(x3)
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Load the curve order n.
     [w13,w12] <= dmem[p384_n] = n */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Compute Solinas constant k for modulus n (we know it is only 191 bits, so
     no need to compute the high part):
     w14 <= 2^256 - n[255:0] = (2^384 - n) mod (2^256) = 2^384 - n */
  bn.sub    w14, w31, w12

  /* initialize w0 <= 0 and w1 <= 0 */
  bn.mov    w0, w31
  bn.mov    w1, w31

  /* Check if modular addition of shares d0 and d1, as well as k0 and k1 is non-zero. */

  /* [w17,w16] <= d = [w5,w4] + [w7,w6] mod n = d0 + d1 mod n */
  bn.add    w18, w4, w6
  bn.addc   w19, w5, w7
  bn.mov    w20, w31
  jal       x1, p384_reduce_n

  /* Compare w16 to 0. */
  bn.cmp    w16, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, 0x7c0, x0
  andi      x2, x2, 8

  /* Compare w17 to 0. */
  bn.cmp    w17, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, 0x7c0, x0
  andi      x3, x3, 8

  /* Check if both registers w16 and w17 are equal to 0.
     x2 AND x3 == 0 <=> [w17,w16] != 0, x2 AND x3 != 0 <=> [w17,w16] == 0 */
  or        x2, x2, x3

  /* If x2 != 0: w0 <= w0 + 1, else: w0 <= w0 + 0 */
  beq       x2, x0, keep_w0_1
  bn.addi   w0, w0, 1
  keep_w0_1:

  /* [w17,w16] <= k = [w9,w8] + [w11,w10] mod n = k0 + k1 mod n */
  bn.add    w18, w8, w10
  bn.addc   w19, w9, w11
  bn.mov    w20, w31
  jal       x1, p384_reduce_n

  /* Compare w16 to 0. */
  bn.cmp    w16, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, 0x7c0, x0
  andi      x2, x2, 8

  /* Compare w17 to 0. */
  bn.cmp    w17, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, 0x7c0, x0
  andi      x3, x3, 8

  /* Check if both registers w16 and w17 are equal to 0.
     x2 AND x3 == 0 <=> [w17,w16] != 0, x2 AND x3 != 0 <=> [w17,w16] == 0 */
  or        x2, x2, x3

  /* If x2 != 0: w0 <= w0 + 1, else: w0 <= w0 + 0 */
  beq       x2, x0, keep_w0_2
  bn.addi   w0, w0, 1
  keep_w0_2:

  /* Compare the values and check if they are distinct to each other.
     If one value pair is equal, then the zero flag will be set.
     In case of an equal pair w1 > 0, otherwise w1 == 0. */

  /* [w21,w20] <= [w5,w4] - [w7,w6] = d0 - d1
     if d0 - d1 == 0: w1 <= w1 + w3 = w1 + 1, else: w1 <= w1 + w31 = w1 + 0 */
  bn.sub    w20, w4, w6
  bn.subb   w21, w5, w7

  /* Compare w20 to 0. */
  bn.cmp    w20, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, 0x7c0, x0
  andi      x2, x2, 8

  /* Compare w21 to 0. */
  bn.cmp    w21, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, 0x7c0, x0
  andi      x3, x3, 8

  /* Check if both registers w20 and w21 are equal to 0.
     x2 AND x3 == 0 <=> [w21,w20] != 0, x2 AND x3 != 0 <=> [w21,w20] == 0 */
  and       x2, x2, x3

  /* If x2 != 0: w1 <= w1 + 1, else: w1 <= w1 + 0 */
  beq       x2, x0, keep_w1_1
  bn.addi   w1, w1, 1
  keep_w1_1:

  /* [w21,w20] <= [w5,w4] - [w9,w8] = d0 - k0
     if d0 - k0 == 0: w1 <= w1 + w3 = w1 + 1, else: w1 <= w1 + w31 = w1 + 0 */
  bn.sub    w20, w4, w8
  bn.subb   w21, w5, w9

  /* Compare w20 to 0. */
  bn.cmp    w20, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, 0x7c0, x0
  andi      x2, x2, 8

  /* Compare w21 to 0. */
  bn.cmp    w21, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, 0x7c0, x0
  andi      x3, x3, 8

  /* Check if both registers w20 and w21 are equal to 0.
     x2 AND x3 == 0 <=> [w21,w20] != 0, x2 AND x3 != 0 <=> [w21,w20] == 0 */
  and       x2, x2, x3

  /* If x2 != 0: w1 <= w1 + 1, else: w1 <= w1 + 0 */
  beq       x2, x0, keep_w1_2
  bn.addi   w1, w1, 1
  keep_w1_2:

  /* [w21,w20] <= [w5,w4] - [w11,w10] = d0 - k1
     if d0 - k1 == 0: w1 <= w1 + w3 = w1 + 1, else: w1 <= w1 + w31 = w1 + 0 */
  bn.sub    w20, w4, w10
  bn.subb   w21, w5, w11

  /* Compare w20 to 0. */
  bn.cmp    w20, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, 0x7c0, x0
  andi      x2, x2, 8

  /* Compare w21 to 0. */
  bn.cmp    w21, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, 0x7c0, x0
  andi      x3, x3, 8

  /* Check if both registers w20 and w21 are equal to 0.
     x2 AND x3 == 0 <=> [w21,w20] != 0, x2 AND x3 != 0 <=> [w21,w20] == 0 */
  and       x2, x2, x3

  /* If x2 != 0: w1 <= w1 + 1, else: w1 <= w1 + 0 */
  beq       x2, x0, keep_w1_3
  bn.addi   w1, w1, 1
  keep_w1_3:

  /* [w21,w20] <= [w7,w6] - [w9,w8] = d1 - k0
     if d1 - k0 == 0: w1 <= w1 + w3 = w1 + 1, else: w1 <= w1 + w31 = w1 + 0 */
  bn.sub    w20, w6, w8
  bn.subb   w21, w7, w9

  /* Compare w20 to 0. */
  bn.cmp    w20, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, 0x7c0, x0
  andi      x2, x2, 8

  /* Compare w21 to 0. */
  bn.cmp    w21, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, 0x7c0, x0
  andi      x3, x3, 8

  /* Check if both registers w20 and w21 are equal to 0.
     x2 AND x3 == 0 <=> [w21,w20] != 0, x2 AND x3 != 0 <=> [w21,w20] == 0 */
  and       x2, x2, x3

  /* If x2 != 0: w1 <= w1 + 1, else: w1 <= w1 + 0 */
  beq       x2, x0, keep_w1_4
  bn.addi   w1, w1, 1
  keep_w1_4:

  /* [w21,w20] <= [w7,w6] - [w11,w10] = d1 - k1
     if d1 - k1 == 0: w1 <= w1 + w3 = w1 + 1, else: w1 <= w1 + w31 = w1 + 0 */
  bn.sub    w20, w6, w10
  bn.subb   w21, w7, w11

  /* Compare w20 to 0. */
  bn.cmp    w20, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, 0x7c0, x0
  andi      x2, x2, 8

  /* Compare w21 to 0. */
  bn.cmp    w21, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, 0x7c0, x0
  andi      x3, x3, 8

  /* Check if both registers w20 and w21 are equal to 0.
     x2 AND x3 == 0 <=> [w21,w20] != 0, x2 AND x3 != 0 <=> [w21,w20] == 0 */
  and       x2, x2, x3

  /* If x2 != 0: w1 <= w1 + 1, else: w1 <= w1 + 0 */
  beq       x2, x0, keep_w1_5
  bn.addi   w1, w1, 1
  keep_w1_5:

  /* [w21,w20] <= [w9,w8] - [w11,w10] = k0 - k1
     if k0 - k1 == 0: w1 <= w1 + w3 = w1 + 1, else: w1 <= w1 + w31 = w1 + 0 */
  bn.sub    w20, w8, w10
  bn.subb   w21, w9, w11

  /* Compare w20 to 0. */
  bn.cmp    w20, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, 0x7c0, x0
  andi      x2, x2, 8

  /* Compare w21 to 0. */
  bn.cmp    w21, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, 0x7c0, x0
  andi      x3, x3, 8

  /* Check if both registers w20 and w21 are equal to 0.
     x2 AND x3 == 0 <=> [w21,w20] != 0, x2 AND x3 != 0 <=> [w21,w20] == 0 */
  and       x2, x2, x3

  /* If x2 != 0: w1 <= w1 + 1, else: w1 <= w1 + 0 */
  beq       x2, x0, keep_w1_6
  bn.addi   w1, w1, 1
  keep_w1_6:

  ecall

.section .data

.balign 32

/* 1st private key share d0 (448-bit) */
d0:
  .zero 64

/* 2nd private key share d1 (448-bit) */
d1:
  .zero 64

/* 1st scalar share k0 (448-bit) */
k0:
  .zero 64

/* 2nd scalar share k1 (448-bit) */
k1:
  .zero 64
