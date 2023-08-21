/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl p384_arithmetic_to_boolean_mod
.globl p384_arithmetic_to_boolean

.text

/**
 * Converts arithmetic shares mod p to boolean shares.
 *
 * Calls the 385-bit A2B function twice, first using unmodified 384-bit shares
 * in reduced form, and then using modified 385-bit shares in unreduced form.
 *
 * It then checks if the MSB (carry bit) is true or false, to decide
 * which of the two A2B results is used. This detects and handles an
 * underflow during the subtraction of arithmetic masking.
 *
 * The logic behind the carry bit handling is as follows:
 * If x >= r, then  A = (x - r) mod p = x - r exactly.
 * So when we add 2^385 - p and then add A and x, we get
 * (2^385 - p + x - r + r) mod 2^385 = 2^385 - p + x.
 * In this case, the high bit is always true since p - x <= p < 2^384,
 * so we choose the A2B conversion without the 2^385 - p added.
 * On the other hand, if x < r, then A = (x - r) mod p = x - r + p.
 * When we add 2^385 - p and then add A and x, we get
 * (2^385 - p + x - r + p + r) mod 2^385 = (2^385 + x) mod 2^385 = x.
 * In this case, the high bit is always false since x < p < 2^384, so we
 * choose this second A2B conversion.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]        w31: all-zero wide data register
 * @param[in]  [w14,w13]: field modulus p
 * @param[in]  [w19,w18]: mask r
 * @param[in]  [w12,w11]: arithmetically masked value A, such that x = A + r
 * @param[out] [w21,w20]: boolean masked value x', such that x = x' ^ r
 *
 * clobbered registers: w1 to w6, w10 to w12, w20, w21, w23 to w28
 * clobbered flag groups: FG0
 */
p384_arithmetic_to_boolean_mod:
  /* First step: calculate A2B from reduced values. */

  /* Save inputs for second A2B execution.
     [w24,w23] <= [w19,w18] = r
     [w26,w25] <= [w12,w11] = A */
  bn.mov    w23, w18
  bn.mov    w24, w19
  bn.mov    w25, w11
  bn.mov    w26, w12

  /* Call 385-bit A2B function.
     [w21,w20] <= x' */
  jal       x1, p384_arithmetic_to_boolean

  /* Save intermediate result of reduced inputs.
     [w28,w27] <= [w21,w20] = x' */
  bn.mov    w27, w20
  bn.mov    w28, w21

  /* Second step: calculate A2B from unreduced values. */

  /* Restore inputs r and A values [w19,w18] and [w12,w11] and
     prepare input for 385-bit A2B function. */
  bn.mov    w18, w23
  bn.mov    w19, w24
  bn.mov    w11, w25
  bn.mov    w12, w26

  /* Convert input A ([w12,w11]) to an unreduced value
     in the 2^385 domain. For this add (2^385 - p) to A.
     [w12,w11] <= [w12,w11] + 2^385 - [w14,w13] = A + 2^385 - p */
  bn.addi   w10, w31, 0x2
  bn.add    w12, w12, w10 << 128
  bn.sub    w11, w11, w13
  bn.subb   w12, w12, w14

  /* Call 385-bit A2B function.
     [w21,w20] <= x' */
  jal       x1, p384_arithmetic_to_boolean

  /* Restore initial mask input of w19 for consistency
     in calling functions.
     w18 <= w23
     w19 <= w24 */
  bn.mov    w18, w23
  bn.mov    w19, w24

  /* Check MSB (carry bit) of second A2B result for true or false. */
  bn.cmp    w31, w21 >> 128

  /* Return the unreduced A2B computation (second result),
     if zero flag is set, otherwise return the reduced
     A2B computation (first result). */
  bn.sel    w20, w20, w27, FG0.Z
  bn.sel    w21, w21, w28, FG0.Z

  ret

/**
 * Convert arithmetic shares to boolean ones using Goubin's algorithm.
 *
 * We use Goubin's boolean-to-arithmetic masking algorithm to switch from
 * an arithmetic masking scheme to a boolean one without ever unmasking the
 * seed. See Algorithm 2 here:
 * https://link.springer.com/content/pdf/10.1007/3-540-44709-1_2.pdf
 *
 * This implementation expands the algorithm to 385 bits for carry bit
 * handling. The carry bit can be used to detect and handle an
 * underflow during the subtraction of arithmetic masking.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w31: all-zero wide data register
 * @param[in]  w18: lower part of mask r
 * @param[in]  w19: upper part of mask r
 * @param[in]  w11: lower part of arithmetically masked value A,
 *                  such that x = A + r
 * @param[in]  w12: upper part of arithmetically masked value A,
 *                  such that x = A + r
 * @param[out] w20: lower part of boolean masked value x',
 *                  such that x = x' ^ r
 * @param[out] w21: upper part of boolean masked value x',
 *                  such that x = x' ^ r
 *
 * clobbered registers: w1 to w6, w11, w12, and w18 to w21
 * clobbered flag groups: FG0
 */
p384_arithmetic_to_boolean:
  /* Initialize inputs: in case of randomness in upper part of inputs
     truncate to 385 bits. */
  bn.rshi   w19, w19, w31 >> 129
  bn.rshi   w19, w31, w19 >> 127
  bn.rshi   w12, w12, w31 >> 129
  bn.rshi   w12, w31, w12 >> 127

  /* Fetch 385 bits of randomness.
     [w2,w1] = gamma    <= URND */
  bn.wsrr   w1, 2
  bn.wsrr   w2, 2
  bn.rshi   w2, w31, w2 >> 127

  /* Double gamma and truncate to 385 bits.
     [w4,w3] = T        <= 2 * [w2,w1] = 2 * gamma */
  bn.add    w3, w1, w1
  bn.addc   w4, w2, w2
  bn.rshi   w4, w4, w31 >> 129
  bn.rshi   w4, w31, w4 >> 127

  /* [w21,w20] = x'     <= [w2,w1] ^ [w19,w18] = gamma ^ r */
  bn.xor    w20, w1, w18
  bn.xor    w21, w2, w19

  /* [w6,w5] = omega    <= [w2,w1] & [w21,w20] = gamma & x' */
  bn.and    w5, w1, w20
  bn.and    w6, w2, w21

  /* [w21,w20] = x'     <= [w4,w3] ^ [w12,w11] = T ^ A */
  bn.xor    w20, w3, w11
  bn.xor    w21, w4, w12

  /* [w2,w1] = gamma    <= [w2,w1] ^ [w21,w20] = gamma ^ x' */
  bn.xor    w1, w1, w20
  bn.xor    w2, w2, w21

  /* [w2,w1] = gamma    <= [w2,w1] & [w19,w18] = gamma & r */
  bn.and    w1, w1, w18
  bn.and    w2, w2, w19

  /* [w6,w5] = omega    <= [w6,w5] ^ [w2,w1] = omega ^ gamma */
  bn.xor    w5, w5, w1
  bn.xor    w6, w6, w2

  /* [w2,w1] = gamma    <= [w4,w3] & [w12,w11] = T & A */
  bn.and    w1, w3, w11
  bn.and    w2, w4, w12

  /* [w6,w5] = omega    <= [w6,w5] ^ [w2,w1] = omega ^ gamma */
  bn.xor    w5, w5, w1
  bn.xor    w6, w6, w2

  /* Loop for k = 1 to K - 1 = 385 - 1 */
  loopi     384, 12

    /* [w2,w1] = gamma  <= [w4,w3] & [w19,w18] = T & r */
    bn.and     w1, w3, w18
    bn.and     w2, w4, w19

    /* [w2,w1] = gamma  <= [w2,w1] ^ [w6,w5] = gamma ^ omega */
    bn.xor     w1, w1, w5
    bn.xor     w2, w2, w6

    /* [w4,w3] = T      <= [w4,w3] & [w12,w11] = T & A */
    bn.and     w3, w3, w11
    bn.and     w4, w4, w12

    /* [w2,w1] = gamma  <= [w2,w1] ^ [w4,w3] = gamma ^ T */
    bn.xor     w1, w1, w3
    bn.xor     w2, w2, w4

    /* Double gamma and truncate to 385 bits.
       [w4,w3] = T      <= 2 * [w2,w1] = 2 * gamma */
    bn.add    w3, w1, w1
    bn.addc   w4, w2, w2
    bn.rshi   w4, w4, w31 >> 129
    bn.rshi   w4, w31, w4 >> 127

  /* [w21,w20] = x'     <= [w21,w20] ^ [w4,w3] = x' ^ T */
  bn.xor    w20, w20, w3
  bn.xor    w21, w21, w4

  ret
