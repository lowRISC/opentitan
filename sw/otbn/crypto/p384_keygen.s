/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   This library contains:
 *   - P-384 specific routines to generate random values for keys and scalars
 */

.section .text

/**
 * Generate a nonzero random value in the scalar field.
 *
 * Returns t, a random value that is nonzero mod n, in shares.
 *
 * This follows a modified version of the method in FIPS 186-4 sections B.4.1
 * and B.5.1 for generation of secret scalar values d and k. The computation
 * in FIPS 186-4 is:
 *   seed = RBG(seedlen) // seedlen >= 448
 *   return (seed mod (n-1)) + 1
 *
 * The important features here are that (a) the seed is at least 64 bits longer
 * than n in order to minimize bias after the reduction and (b) the resulting
 * scalar is guaranteed to be nonzero.
 *
 * We deviate from FIPS a little bit here because for side-channel protection,
 * we do not want to fully reduce the seed modulo (n-1) or combine the shares.
 * Instead, we do the following:
 *   seed0 = RBG(448)
 *   seed1 = RBG(448)
 *   x = URND(127) + 1 // random value for masking
 *   if (seed0 * x + seed1 * x) mod n == 0:
 *     retry
 *   return seed0, seed1
 *
 * Essentially, we get two independent seeds and interpret these as additive
 * shares of the scalar t = (seed0 + seed1) mod n. Then, we need to ensure t is
 * nonzero. Multiplying each share with a random masking parameter allows us to
 * safely add them, and then check if this result is 0; if it is, then t must
 * be 0 mod n and we need to retry.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]           w31:  all-zero
 * @param[in]  dmem[p384_n]:  Curve order n
 * @param[out]      [w7,w6]:  first share of secret scalar t (448 bits)
 * @param[out]      [w9,w8]:  second share of secret scalar t (448 bits)
 *
 * clobbered registers: x2, x3, w4 to w11, w14, w16 to w28
 * clobbered flag groups: FG0
 */
p384_random_scalar:
  /* Load the curve order n.
     [w13,w12] <= dmem[p384_n] = n */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  random_scalar_retry:
  /* Obtain 1024 bits of randomness from RND. */
  bn.wsrr   w6, RND
  bn.wsrr   w7, RND
  bn.wsrr   w8, RND
  bn.wsrr   w9, RND

  /* XOR with bits from URND, just in case there's any vulnerability in EDN
     that lets the attacker recover bits before they reach OTBN. */
  bn.wsrr   w5, URND
  bn.xor    w6, w6, w5
  bn.wsrr   w5, URND
  bn.xor    w7, w7, w5
  bn.wsrr   w5, URND
  bn.xor    w8, w8, w5
  bn.wsrr   w5, URND
  bn.xor    w9, w9, w5

  /* Shift bits to get 448-bit seeds.
     seed0 = [w7,w6], seed1 = [w9,w8]
     w7 <= w7[192:0]
     w9 <= w9[192:0] */
  bn.rshi   w7, w31, w7 >> 64
  bn.rshi   w9, w31, w9 >> 64

  /* Compute Solinas constant k for modulus n (we know it is only 191 bits, so
     no need to compute the high part):
     w14 <= 2^256 - n[255:0] = (2^384 - n) mod (2^256) = 2^384 - n */
  bn.sub    w14, w31, w12

  /* Generate a random 127-bit number.
     w4 <= URND()[255:129] */
  bn.wsrr   w4, URND
  bn.rshi   w4, w31, w4 >> 129

  /* Add 1 to get a 128-bit nonzero scalar for masking.
     w4 <= w4 + 1 = x */
  bn.addi   w4, w4, 1

  /* [w26,w25] <= ([w7,w6] * w4) mod n = (seed0 * x) mod n */
  bn.mov    w16, w4
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, p384_mulmod448x128_n
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* [w28,w27] <= ([w9,w8] * w4) mod n = (seed1 * x) mod n */
  bn.mov    w16, w4
  bn.mov    w10, w8
  bn.mov    w11, w9
  jal       x1, p384_mulmod448x128_n
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* Compute (seed * x) mod n = (seed0 * x + seed1 * x) mod n
     [w17,w16] <= seed * x = [w26,w25] + [w28,w27] mod n */
  bn.add    w18, w27, w25
  bn.addc   w19, w28, w26
  bn.mov    w20, w31
  jal       x1, p384_reduce_n

  /* Compare w16 to 0. */
  bn.cmp    w16, w31

  /* Read the FG0.Z flag (position 3).
     x2 <= 8 if FG0.Z else 0 */
  csrrw     x2, FG0, x0
  andi      x2, x2, 8

  /* Compare w17 to 0. */
  bn.cmp    w17, w31

  /* Read the FG0.Z flag (position 3).
     x3 <= 8 if FG0.Z else 0 */
  csrrw     x3, FG0, x0
  andi      x3, x3, 8

  /* Check if both registers w16 and w17 are equal to 0.
     x2 AND x3 == 0 <=> [w17,w16] != 0, x2 AND x3 != 0 <=> [w17,w16] == 0 */
  or        x2, x2, x3

  /* Retry if x2 != 0. */
  bne       x2, x0, random_scalar_retry

  /* If we get here, then (seed0 + seed1) mod n is nonzero mod n; return. */

  ret

/**
 * Generate the secret key d from a random seed.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x20: dptr_d0, pointer to bufffer of 1st private key share d0
 * @param[in]  x21: dptr_d1, pointer to bufffer of 2nd private key share d1
 *
 * clobbered registers: x2, x3, x20, w4 to w11, w14, w16 to w28
 * clobbered flag groups: FG0
 */
.globl p384_generate_random_key
p384_generate_random_key:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Generate a random scalar in two 448-bit shares.
     [w7,w6] <= d0
     [w9,w8] <= d1 */
  jal  x1, p384_random_scalar

  /* Write first share to DMEM.
     dmem[d0] <= [w7,w6] = d0 */
  li        x2, 6
  bn.sid    x2++, 0(x20)
  bn.sid    x2++, 32(x20)

  /* Write second share to DMEM.
     dmem[d1] <= [w9,w8] = d1 */
  bn.sid    x2++, 0(x21)
  bn.sid    x2++, 32(x21)

  ret

/**
 * Generate the secret scalar k from a random seed.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x20: dptr_k0, pointer to bufffer of 1st scalar share k0
 * @param[in]  x21: dptr_k1, pointer to bufffer of 2nd scalar share k1
 *
 * clobbered registers: x2, x3, x20, w4 to w11, w14, w16 to w28
 * clobbered flag groups: FG0
 */
.globl p384_generate_k
p384_generate_k:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Generate a random scalar in two 448-bit shares.
     [w7,w6] <= k0
     [w9,w8] <= k1 */
  jal  x1, p384_random_scalar

  /* Write first share to DMEM.
     dmem[k0] <= [w7,w6] = k0 */
  li        x2, 6
  bn.sid    x2++, 0(x20)
  bn.sid    x2++, 32(x20)

  /* Write second share to DMEM.
     dmem[k1] <= [w9,w8] = k1 */
  bn.sid    x2++, 0(x21)
  bn.sid    x2++, 32(x21)

  ret
