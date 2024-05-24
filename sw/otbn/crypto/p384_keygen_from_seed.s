/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   This library contains:
 *   - P-384 specific routines to generate a random private key from
 *     a sideloaded seed.
 */

.section .text

/**
 * P-384 ECC secret key generation.
 *
 * Returns the secret key d in two 448-bit shares d0 and d1, such that:
 *    d = (d0 + d1) mod n
 * ...where n is the curve order.
 *
 * This implementation follows FIPS 186-5 section A.2.1, where we
 * generate d using a 384-bit seed. But while FIPS computes
 * d = (seed mod (n-1)) + 1 to ensure a nonzero key, we
 * instead just compute d = seed mod n. The caller MUST ensure that if this
 * routine is used, then other routines that use d (e.g. signing, public key
 * generation) are checking if d is 0.
 * To generate 448-bit key shares, we just take 63 bits from RND multiplied by n
 * and then added to the seed shares. (63 bits to prevent overflow.)
 *
 * Most complexity in this routine comes from masking. The input seed is
 * provided in two 384-bit shares, seed0 and seed1, such that:
 *   seed = seed0 ^ seed1
 * Bits at position 384 and above in the input shares will be ignored.
 *
 * We then use Goubin's boolean-to-arithmetic masking algorithm to switch from
 * this boolean masking scheme to an arithmetic one without ever unmasking the
 * seed. See Algorithm 1 here:
 * https://link.springer.com/content/pdf/10.1007/3-540-44709-1_2.pdf
 *
 * For a Coq proof of the correctness of the basic computational logic here
 * see:
 *   https://gist.github.com/jadephilipoom/24f44c59cbe59327e2f753867564fa28#file-masked_reduce-v-L226
 *
 * The proof does not cover leakage properties; it mostly just shows that this
 * logic correctly computes (seed mod n) and the carry-handling works.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]     [w21, w20]: seed0, first share of seed (384 bits)
 * @param[in]     [w11, w10]: seed1, second share of seed (384 bits)
 * @param[in]            w31: all-zero
 * @param[out]      dmem[d0]: d0, first share of private key d (448 bits)
 * @param[out]      dmem[d1]: d1, second share of private key d (448 bits)
 *
 * clobbered registers: x2, x3, x20, w1 to w6, w16 to w29
 * clobbered flag groups: FG0
 */
.globl p384_key_from_seed
p384_key_from_seed:
  /* Convert from a boolean to an arithmetic mask using Goubin's algorithm.
       [w21, w20] <= ((seed0 ^ seed1) - seed1) mod 2^385 = x0 */
  jal       x1, p384_boolean_to_arithmetic

  /* At this point, we have arithmetic shares modulo 2^385:
       [w21, w20] : x0
       [w11, w10] : x1

     We know that x1=seed1, and seed and x1 are at most 384 bits. Therefore,
     the highest bit of x0 holds a carry bit modulo 2^384:
       x0 = (seed - x1) mod 2^385
       x0 = (seed - x1) mod 2^384 + (if (x1 <= seed) then 0 else 2^384)

     The carry bit then allows us to replace (mod 2^385) with a conditional
     statement:
       seed = (x0 mod 2^384) + x1 - (x0[384] << 384)

     Note that the carry bit is not very sensitive from a side channel
     perspective; x1 <= seed has some bias related to the highest bit of the
     seed.

     From here, we want to convert to shares modulo n.
     We compute the new shares as follows:
       c = (x0[384] << 384) mod n
       d0 = (x0 mod 2^384) - c) mod n
       d1 = x1 mod n

       d = seed mod n = (d0 + d1) mod n
  */

  /* Load curve order n from DMEM.
       [w17,w16] <= dmem[p384_n] = n */
  li        x2, 16
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* [w25,w24] <= (x1 - n) mod 2^512 */
  bn.sub    w24, w10, w16
  bn.subb   w25, w11, w17

  /* Compute d1. Because 2^384 < 2 * n, a conditional subtraction is
     sufficient to reduce. Similarly to the carry bit, the conditional bit here
     is not very sensitive because the shares are large relative to n.
       [w6,w5] <= x1 mod n = d1 */
  bn.sel    w5, w10, w24, FG0.C
  bn.sel    w6, w11, w25, FG0.C

  /* Isolate the carry bit and shift it back into position.
       w25 <= x0[384] << 128 */
  bn.rshi   w25, w31, w21 >> 128
  bn.rshi   w25, w25, w31 >> 128

  /* Clear the carry bit from the original result.
       [w21,w20] <= x0 mod 2^384 */
  bn.xor    w21, w21, w25

  /* Conditionally subtract n to reduce.
       [w21,w20] <= (x0 mod 2^384) mod n */
  bn.sub    w26, w20, w16
  bn.subb   w27, w21, w17
  bn.sel    w20, w20, w26, FG0.C
  bn.sel    w21, w21, w27, FG0.C

  /* Compute the correction factor.
       [w25,w24] <= (x[384] << 384) mod n = c */
  bn.sub    w26, w31, w16
  bn.subb   w27, w25, w17
  bn.sel    w24, w31, w26, FG0.C
  bn.sel    w25, w25, w27, FG0.C

  /* Compute d0 with a modular subtraction. First we add n to protect
     against underflow, then conditionally subtract it again if needed.
       [w23,w22] <= ([w21, w20] - [w25,w24]) mod n = d0 */
  bn.add    w20, w20, w16
  bn.addc   w21, w21, w17
  bn.sub    w20, w20, w24
  bn.subb   w21, w21, w25
  bn.sub    w26, w20, w16
  bn.subb   w27, w21, w17
  bn.sel    w22, w20, w26, FG0.C
  bn.sel    w23, w21, w27, FG0.C

  /* Get 63 bits of randomness from RND, multiply it with n,
     and add it to the key share to get a 448-bit share. */

  /* [w2,w1] <= (RND >> 193) * n */
  bn.wsrr   w10, RND
  bn.rshi   w10, w31, w10 >> 193
  bn.mov    w11, w31
  jal       x1, mul384
  bn.mov    w1, w18
  bn.mov    w2, w19

  /* [w6,w5] <= [w6,w5] + [w2,w1] = d1 + (RND >> 193) * n = d1' */
  bn.add    w5, w5, w1
  bn.addc   w6, w6, w2

  /* [w4,w3] <= (RND >> 193) * n */
  bn.wsrr   w10, RND
  bn.rshi   w10, w31, w10 >> 193
  bn.mov    w11, w31
  jal       x1, mul384
  bn.mov    w3, w18
  bn.mov    w4, w19

  /* [w23,w22] <= [w23,w22] + [w4,w3] = d0 + (RND >> 193) * n = d0' */
  bn.add    w22, w22, w3
  bn.addc   w23, w23, w4

  /* Write first 448-bit share to DMEM.
     dmem[d0] <= [w23,w22] = d0' */
  la        x20, d0
  li        x2, 22
  bn.sid    x2++, 0(x20)
  bn.sid    x2++, 32(x20)

  /* Write second 448-bit share to DMEM.
     dmem[d1] <= [w6,w5] = d1' */
  la        x20, d1
  li        x2, 5
  bn.sid    x2++, 0(x20)
  bn.sid    x2++, 32(x20)

  ret

.section .data

.balign 32

/* 1st private key share d0 */
.globl d0
.weak d0
d0:
  .zero 64

/* 2nd private key share d1 */
.globl d1
.weak d1
d1:
  .zero 64
