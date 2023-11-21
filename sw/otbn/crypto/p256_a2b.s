/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl arithmetic_to_boolean_mod
.globl arithmetic_to_boolean

.text

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
 * So when we add 2^257 - p and then add A and x, we get
 * (2^257 - p + x - r + r) mod 2^257 = 2^257 - p + x.
 * In this case, the high bit is always true since p - x <= p < 2^256,
 * so we choose the A2B conversion without the 2^257 - p added.
 * On the other hand, if x < r, then A = (x - r) mod p = x - r + p.
 * When we add 2^257 - p and then add A and x, we get
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

  /* Save inputs for second A2B execution.
     w24 <= w19 = r
     w25 <= w11 = A */
  bn.mov    w24, w19
  bn.mov    w25, w11

  /* Expand inputs r and A (w19 and w11) to 257-bit values [w19,w18]
     and [w12,w11] and prepare input for 257-bit A2B function.
     w18 <= w19
     w19 <= w31
     w11 <= w11 -> obsolete
     w12 <= w31 */
  bn.mov    w18, w19
  bn.mov    w19, w31
  bn.mov    w12, w31

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
     [w12,w11] <= [w12,w11] - w29 = (A + 2^257) - p */
  bn.addi   w12, w12, 0x2
  bn.sub    w11, w11, w29
  bn.subb   w12, w12, w31

  /* Call 257-bit A2B function.
     [w21,w20] <= x' */
  jal       x1, arithmetic_to_boolean

  /* Restore initial mask input of w19 for consistency
     in calling functions.
     w19 <= w24 */
  bn.mov    w19, w24

  /* Check MSB (carry bit) of second A2B result for true or false. */
  bn.cmp    w21, w31 /* w21 can only be 0x1 or 0x0 */

  /* Return the unreduced A2B computation (second result),
     if zero flag is set, otherwise return the reduced
     A2B computation (first result). */
  bn.sel    w20, w20, w26, FG0.Z

  ret

/**
 * Convert arithmetic shares to boolean ones using Goubin's algorithm.
 *
 * We use Goubin's boolean-to-arithmetic masking algorithm to switch from
 * an arithmetic masking scheme to a boolean one without ever unmasking the
 * seed. See Algorithm 2 here:
 * https://link.springer.com/content/pdf/10.1007/3-540-44709-1_2.pdf
 *
 * This implementation expands the algorithm to 257 bits for carry bit
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
 * clobbered registers: w1 - w6, w11, w12, and w18 - w21
 * clobbered flag groups: FG0
 */
arithmetic_to_boolean:
  /* Initialize inputs: in case of randomness in upper part of inputs
     truncate to 257 bits. */
  bn.rshi   w19, w19, w31 >> 1
  bn.rshi   w19, w31, w19 >> 255
  bn.rshi   w12, w12, w31 >> 1
  bn.rshi   w12, w31, w12 >> 255

  /* Fetch 257 bits of randomness.
     [w2,w1] = gamma    <= URND */
  bn.wsrr   w1, 2
  bn.wsrr   w2, 2
  bn.rshi   w2, w31, w2 >> 255

  /* Double gamma and truncate to 257 bits.
     [w4,w3] = T        <= 2 * [w2,w1] = 2 * gamma */
  bn.add    w3, w1, w1
  bn.addc   w4, w2, w2
  bn.rshi   w4, w4, w31 >> 1
  bn.rshi   w4, w31, w4 >> 255

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

  /* Loop for k = 1 to K - 1 = 257 - 1 */
  loopi     256, 12

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

    /* Double gamma and truncate to 257 bits.
       [w4,w3] = T      <= 2 * [w2,w1] = 2 * gamma */
    bn.add    w3, w1, w1
    bn.addc   w4, w2, w2
    bn.rshi   w4, w4, w31 >> 1
    bn.rshi   w4, w31, w4 >> 255

  /* [w21,w20] = x'     <= [w21,w20] ^ [w4,w3] = x' ^ T */
  bn.xor    w20, w20, w3
  bn.xor    w21, w21, w4

  ret
