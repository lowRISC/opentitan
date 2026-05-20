/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl boolean_to_arithmetic

.text


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
 * clobbered registers: w1 to w4, w11, w20, w21, w28, and w29
 * clobbered flag groups: FG0
 */
boolean_to_arithmetic:
  /* Mask out excess bits from seed shares.
       [w21, w20] <= s0 mod 2^320
       [w11, w10] <= s1 mod 2^320 = x1 */
  bn.rshi   w21, w21, w31 >> 64
  bn.rshi   w21, w31, w21 >> 192
  bn.rshi   w31, w31, w31 >> 192  /* dummy instruction to flush ALU datapath */
  bn.rshi   w11, w11, w31 >> 64
  bn.rshi   w11, w31, w11 >> 192

  /* Fetch 321 bits of randomness from URND.
       [w2, w1] <= gamma */
  bn.wsrr   w1, URND
  bn.wsrr   w2, URND
  bn.rshi   w2, w31, w2 >> 191

  /* [w4, w3] <= [w21, w20] ^ [w2, w1] = s0 ^ gamma */
  bn.xor    w3, w20, w1
  bn.xor    w4, w21, w2

  /* Subtract gamma. This may result in bits above 2^321, but these will be
     stripped off in the next step.
       [w4, w3] <= [w4, w3] - [w2, w1] = ((s0 ^ gamma) - gamma) mod 2^512 */
  bn.sub    w3, w3, w1
  bn.subb   w4, w4, w2
  bn.sub    w31, w31, w31  /* dummy instruction to clear flags */

  /* Truncate subtraction result to 321 bits.
       [w4, w3] <= [w4, w3] mod 2^321 = T */
  bn.rshi   w4, w4, w31 >> 65
  bn.rshi   w4, w31, w4 >> 191

  /* [w4, w3] <= [w4, w3] ^ [w21, w20] = T2 */
  bn.xor    w3, w3, w20
  bn.xor    w4, w4, w21

  /* [w2, w1] <= [w2, w1] ^ [w11, w10] = gamma ^ s1 = G */
  bn.xor    w1, w10, w1
  bn.xor    w2, w2, w11

  /* [w21, w20] <= [w21, w20] ^ [w2, w1] = s0 ^ G */
  bn.xor    w20, w20, w1
  bn.xor    w21, w21, w2

  /* [w21, w20] <= [w21, w20] - [w2, w1] = ((s0 ^ G) - G) mod 2^512 */
  bn.sub    w20, w20, w1
  bn.subb   w21, w21, w2
  bn.sub    w31, w31, w31  /* dummy instruction to clear flags */

  /* [w21, w20] <= [w21, w20] mod 2^321 = A */
  bn.rshi   w21, w21, w31 >> 65
  bn.rshi   w21, w31, w21 >> 191

  /* apply fresh mask to w20 and w21 before xoring with w3 and w4 */
  bn.wsrr   w28, RND
  bn.wsrr   w29, RND
  bn.xor    w20, w28, w20
  bn.xor    w21, w29, w21

  /* [w21, w20] <= [w21, w20] ^ [w4, w3] = A ^ T2 = x0 */
  bn.xor    w20, w20, w3
  bn.xor    w21, w21, w4

  /* remove fresh mask */
  bn.xor    w20, w28, w20
  bn.xor    w21, w29, w21
  bn.xor    w31, w31, w31  /* dummy instruction to clear flags */

  ret
