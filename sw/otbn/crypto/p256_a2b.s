/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl arithmetic_to_boolean

.text


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
 * clobbered registers: w1 - w6, w12, and w19 - w21
 * clobbered flag groups: FG0
 */
arithmetic_to_boolean:
  /* Initialize inputs: in case of randomness in upper part of inputs
     truncate to 257 bits. Also, fetch 257 bits of randomness.

     N.B. Accesses to w19 and w12 have been intentionally made non-sequential to
     avoid transient side channel leakage.

     [w2,w1] = gamma    <= URND */

  bn.rshi   w19, w19, w31 >> 1
  bn.rshi   w19, w31, w19 >> 255
  bn.wsrr   w1, URND
  bn.wsrr   w2, URND
  bn.rshi   w2, w31, w2 >> 255
  bn.rshi   w12, w12, w31 >> 1
  bn.rshi   w12, w31, w12 >> 255

  /* Double gamma and truncate to 257 bits.
     [w4,w3] = T        <= 2 * [w2,w1] = 2 * gamma */
  bn.add    w3, w1, w1
  bn.addc   w4, w2, w2
  bn.rshi   w4, w4, w31 >> 1
  bn.rshi   w4, w31, w4 >> 255

  /* [w21,w20] = x'     <= [w2,w1] ^ [w19,w18] = gamma ^ r

     N.B. The dummy instruction below is to clear the flags from performing
     the XORs, as their input in w18 and w19 is the secret share r. */
  bn.xor    w20, w1, w18
  bn.xor    w21, w2, w19
  bn.xor    w31, w31, w31  /* dummy instruction to clear flags */

  /* [w6,w5] = omega    <= [w2,w1] & [w21,w20] = gamma & x' */
  bn.and    w5, w1, w20
  bn.and    w6, w2, w21

  /* [w21,w20] = x'     <= [w4,w3] ^ [w12,w11] = T ^ A

     N.B. The dummy instruction below is to clear the flags from performing
     the XORs, as their input in w11 and w12 is the secret share A. */
  bn.xor    w20, w3, w11
  bn.xor    w21, w4, w12
  bn.xor    w31, w31, w31  /* dummy instruction to clear flags */

  /* [w2,w1] = gamma    <= [w2,w1] ^ [w21,w20] = gamma ^ x' */
  bn.xor    w1, w1, w20
  bn.xor    w2, w2, w21

  /* [w2,w1] = gamma    <= [w2,w1] & [w19,w18] = gamma & r

     N.B. The dummy instruction below is to clear the flags from performing
     the XORs, as their input in w18 and w19 is the secret share r. */
  bn.and    w1, w1, w18
  bn.and    w2, w2, w19
  bn.xor    w31, w31, w31  /* dummy instruction to clear flags */

  /* [w6,w5] = omega    <= [w6,w5] ^ [w2,w1] = omega ^ gamma */
  bn.xor    w5, w5, w1
  bn.xor    w6, w6, w2

  /* [w2,w1] = gamma    <= [w4,w3] & [w12,w11] = T & A

     N.B. The dummy instruction below is to clear the flags from performing
     the XORs, as their input in w11 and w12 is the secret share A. */
  bn.and    w1, w3, w11
  bn.and    w2, w4, w12
  bn.xor    w31, w31, w31  /* dummy instruction to clear flags */

  /* [w6,w5] = omega    <= [w6,w5] ^ [w2,w1] = omega ^ gamma */
  bn.xor    w5, w5, w1
  bn.xor    w6, w6, w2

  /* Loop for k = 1 to K - 1 = 257 - 1 */
  loopi     256, 14

    /* [w2,w1] = gamma  <= [w4,w3] & [w19,w18] = T & r

       N.B. The dummy instruction below is to clear the flags from performing
       the XORs, as their input in w18 and w19 is the secret share r. */
    bn.and     w1, w3, w18
    bn.and     w2, w4, w19
    bn.xor     w31, w31, w31  /* dummy instruction to clear flags */

    /* [w2,w1] = gamma  <= [w2,w1] ^ [w6,w5] = gamma ^ omega */
    bn.xor     w1, w1, w5
    bn.xor     w2, w2, w6

    /* [w4,w3] = T      <= [w4,w3] & [w12,w11] = T & A

       N.B. The dummy instruction below is to clear the flags from performing
       the XORs, as their input in w11 and w12 is the secret share A. */
    bn.and     w3, w3, w11
    bn.and     w4, w4, w12
    bn.xor     w31, w31, w31  /* dummy instruction to clear flags */

    /* [w2,w1] = gamma  <= [w2,w1] ^ [w4,w3] = gamma ^ T */
    bn.xor     w1, w1, w3
    bn.xor     w2, w2, w4

    /* Double gamma and truncate to 257 bits.
       [w4,w3] = T      <= 2 * [w2,w1] = 2 * gamma */
    bn.add    w3, w1, w1
    bn.addc   w4, w2, w2
    bn.rshi   w4, w4, w31 >> 1
    bn.rshi   w4, w31, w4 >> 255

  /* [w21,w20] = x'     <= [w21,w20] ^ [w4,w3] = x' ^ T

     N.B. The dummy instruction below is to clear the flags from performing
     the XORs, as their result in w20 and w21 is the secret share x'. */
  bn.xor    w20, w20, w3
  bn.xor    w21, w21, w4
  bn.xor    w31, w31, w31  /* dummy instruction to clear flags */

  ret
