/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl share_scalar

/**
 * Convert boolean shares to arithmetic ones using Goubin's algorithm.
 *
 * Returns x0, x1 such that (s0 ^ s1) = (x0 + x1) mod 2^321.
 *
 * This is a variant of the `boolean_to_arithmetic` for P-256.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w21, w20]: s0, first share of seed (320 bits)
 * @param[in]  [w11, w10]: s1, second share of seed (320 bits)
 * @param[in]         w31: all-zero
 * @param[out] [w21, w20]: result x0 (321 bits)
 * @param[out] [w11, w10]: result x1 (320 bits)
 *
 * clobbered registers: w20 to w29
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
       [w25, w24] <= gamma */
  bn.wsrr   w24, URND
  bn.wsrr   w25, URND
  bn.rshi   w25, w31, w25 >> 191

  /* [w27, w26] <= [w21, w20] ^ [w25, w24] = s0 ^ gamma */
  bn.xor    w26, w20, w24
  bn.xor    w27, w21, w25

  /* Subtract gamma. This may result in bits above 2^321, but these will be
     stripped off in the next step.
       [w27, w26] <= [w27, w26] - [w25, w24] = ((s0 ^ gamma) - gamma) mod 2^512 */
  bn.sub    w26, w26, w24
  bn.subb   w27, w27, w25
  bn.sub    w31, w31, w31  /* dummy instruction to clear flags */

  /* Truncate subtraction result to 321 bits.
       [w27, w26] <= [w27, w26] mod 2^321 = T */
  bn.rshi   w27, w27, w31 >> 65
  bn.rshi   w27, w31, w27 >> 191

  /* [w27, w26] <= [w27, w26] ^ [w21, w20] = T2 */
  bn.xor    w26, w26, w20
  bn.xor    w27, w27, w21

  /* [w25, w24] <= [w25, w24] ^ [w11, w10] = gamma ^ s1 = G */
  bn.xor    w24, w24, w10
  bn.xor    w25, w25, w11

  /* [w21, w20] <= [w21, w20] ^ [w25, w24] = s0 ^ G */
  bn.xor    w20, w20, w24
  bn.xor    w21, w21, w25

  /* [w21, w20] <= [w21, w20] - [w25, w24] = ((s0 ^ G) - G) mod 2^512 */
  bn.sub    w20, w20, w24
  bn.subb   w21, w21, w25
  bn.sub    w31, w31, w31  /* dummy instruction to clear flags */

  /* [w21, w20] <= [w21, w20] mod 2^321 = A */
  bn.rshi   w21, w21, w31 >> 65
  bn.rshi   w21, w31, w21 >> 191

  /* apply fresh mask to w20 and w21 before xoring with w3 and w27 */
  bn.wsrr   w28, RND
  bn.wsrr   w29, RND
  bn.xor    w20, w28, w20
  bn.xor    w21, w29, w21

  /* [w21, w20] <= [w21, w20] ^ [w27, w3] = A ^ T2 = x0 */
  bn.xor    w20, w20, w26
  bn.xor    w21, w21, w27

  /* remove fresh mask */
  bn.xor    w20, w28, w20
  bn.xor    w21, w29, w21
  bn.xor    w31, w31, w31  /* dummy instruction to clear flags */

  ret

/**
 * Arithmetically share a Boolean-masked Ed25519 secret key.
 *
 * This is a variant of the `p256_key_from_seed` routine for P-256.
 *
 * Returns the secret key d in two 320-bit shares d0 and d1, such that:
 *    d = (d0 + d1) mod n
 * ...where n is the curve order.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w21, w20]: seed0, first share of seed (320 bits)
 * @param[in]  [w11, w10]: seed1, second share of seed (320 bits)
 * @param[in]         w31: all-zero
 * @param[out] [w21, w20]: d0, first share of private key d (320 bits)
 * @param[out] [w11, w10]: d1, second share of private key d (320 bits)
 *
 * clobbered registers: x2, x3, w20 to w29
 * clobbered flag groups: FG0
 */
share_scalar:
  /* Convert from a boolean to an arithmetic mask using Goubin's algorithm.
       [w21, w20] <= ((seed0 ^ seed1) - seed1) mod 2^321 = x0 */
  jal       x1, boolean_to_arithmetic

  /* At this point, we have arithmetic shares modulo 2^321:
       [w21, w20] : x0
       [w11, w10] : x1

     We know that x1=seed1, and seed and x1 are at most 320 bits. Therefore,
     the highest bit of x0 holds a carry bit modulo 2^320:
       x0 = (seed - x1) mod 2^321
       x0 = (seed - x1) mod 2^320 + (if (x1 <= seed) then 0 else 2^320)

     The carry bit then allows us to replace (mod 2^321) with a conditional
     statement:
       seed = (x0 mod 2^320) + x1 - (x0[320] << 320)

     Note that the carry bit is not very sensitive from a side channel
     perspective; x1 <= seed has some bias related to the highest bit of the
     seed, but since the seed is 64 bits larger than n, this single-bit noisy
     leakage should not be significant.

     From here, we want to convert to shares modulo (n * 2^64) -- these shares
     will be equivalent to the seed modulo n but still retain 64 bits of extra
     masking. We compute the new shares as follows:
       c = (x0[320] << 320) mod (n << 64)
       d0 = ((x0 mod 2^320) - c) mod (n << 64))
       d1 = x1 mod (n << 64)

       d = seed mod n = (d0 + d1) mod n
  */

  /* Load curve order n from DMEM.
       w29 <= dmem[ed25519_scalar_L] = L */
  li        x2, 29
  la        x3, ed25519_scalar_L
  bn.lid    x2, 0(x3)

  /* Compute (L << 67).
       [w29,w28] <= w29 << 67 = L << 67 */
  bn.rshi   w28, w29, w31 >> 189
  bn.rshi   w29, w31, w29 >> 189

  /* [w25,w24] <= (x1 - (L << 67)) mod 2^512 */
  bn.sub    w24, w10, w28
  bn.subb   w25, w11, w29

  /* Compute d1. Because 2^320 < 2 * (n << 64), a conditional subtraction is
     sufficient to reduce. Similarly to the carry bit, the conditional bit here
     is not very sensitive because the shares are large relative to n.

     N.B. Even though the conditional bit isn't sensitive here, other flags set
     by the above subtraction (i.e. the LSB flag) may be; the dummy instruction
     below serves both to clear these flags as well as to separate instructions
     accessing w11 and w21 respectively, as these form the upper words of a
     pair of secret shares.

       [w11,w10] <= x1 mod (L << 67) = d1 */
  bn.sel    w10, w10, w24, FG0.C
  bn.sel    w11, w11, w25, FG0.C
  bn.sub    w23, w23, w23  /* dummy instruction to clear flags */

  /* Isolate the carry bit and shift it back into position.
       w25 <= x0[320] << 67 */
  bn.rshi   w25, w31, w21 >> 64
  bn.rshi   w25, w25, w31 >> 192

  /* Clear the carry bit from the original result.
       [w21,w20] <= x0 mod 2^320 */
  bn.xor    w21, w21, w25

  /* Conditionally subtract (L << 67) to reduce.
       [w21,w20] <= (x0 mod 2^320) mod (L << 67) */
  bn.sub    w26, w20, w28
  bn.subb   w27, w21, w29
  bn.sel    w20, w20, w26, FG0.C
  bn.sel    w21, w21, w27, FG0.C

  /* Compute the correction factor.
       [w25,w24] <= (x[320] << 320) mod (L << 67) = c */
  bn.sub    w26, w31, w28
  bn.subb   w27, w25, w29
  bn.sel    w24, w31, w26, FG0.C
  bn.sel    w25, w25, w27, FG0.C

  /* Compute d0 with a modular subtraction. First we add (L << 67) to protect
     against underflow, then conditionally subtract it again if needed.

     N.B. we also insert a dummy instruction at the end of this routine, as
     the flags set will reveal information regarding the partial share in w21
     in the case that the final conditional subtraction is performed.

       [w21,w20] <= ([w21, w20] - [w25,w24]) mod (L << 67) = d0 */
  bn.add    w20, w20, w28
  bn.addc   w21, w21, w29
  bn.sub    w20, w20, w24
  bn.subb   w21, w21, w25
  bn.sub    w26, w20, w28
  bn.subb   w27, w21, w29
  bn.sel    w20, w20, w26, FG0.C
  bn.sel    w21, w21, w27, FG0.C
  bn.sub    w23, w23, w23  /* dummy instruction to clear flags */

  ret
