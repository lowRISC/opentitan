/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.text
.globl check_primality

/**
 * Prbabilistic primality test using a hardened modular exponentations.
 *
 * The test is composed of a Fermat Test a^(p-1) mod p followed by multiple
 * rounds of the Miller-Rabin test.
 *
 * Same API as `modexp`, prime candidate resides in DMEM[dptr_d0].
 *
 * XXX: Make this more ergonomical.
 *
 * @param[in]  x23: dptr_r0, DMEM pointer to the input A and output C
 * @param[in]  x24: dptr_r1, DMEM pointer to a tmp location of size 512 bytes
 * @param[in]  x25: dptr_r2, DMEM pointer to a tmp location of size 512 bytes
 * @param[in]  x26: dptr_d0, DMEM pointer to the first share of exponent d
 * @param[in]  x27: dptr_d1, DMEM pointer to the second share of the exponent d
 * @param[in]  x28: dptr_n,  DMEM pointer to the modulus M
 * @param[in]  x29: dptr_rr, DMEM pointer to RR = R^2 mod M
 * @param[in]  x30: N, number of limbs per bignum
 * @param[in]   w1: Montgomery Constant m0'
 * @param[in]  w31: all-zero
 * @param[out] w24: result, all 1s if the check passed and 0 otherwise
 */
check_primality:
  /* x31 = x30 - 1 = N - 1. */
  addi      x31, x30, -1

/**********************************************************
 * Begin GCD Test
 **********************************************************/

  /*
   * Check whether gcd(F4, p-1) == 1. This is only relevant for the RSA prime
   * generation routine and not for general primality tests.
   *
   * XXX: Move this out of here.
   */
  addi x16, x26, 0
  jal x1, relprime_f4

  /* relprime_f4 returns w24 = 2^256-1 if gcd(p-1, e) == 1. */
  bn.cmp   w24, w31, FG0
  csrrs    x2, FG0, x0
  andi     x2, x2, 8
  bne      x2, x0, _check_primality_fail

/**********************************************************
 * End GCD Test
 **********************************************************/

/**********************************************************
 * Begin Fermat Test
 **********************************************************/

  /*
   * For a random  witness a that is not 0 and is not divisible by p, we have
   *  `a^(p-1) = 1 mod p`, if p is a prime number. This filters out a first
   *  batch of composite numbers. Those that remain are either prime or a
   * Carmichael Number for which the subsequent Miller-Rabin Test is needed.
   */

  /*
   * Load the Montgomery constants.
   *
   * XXX: Does this leak p?
   */
  addi x16, x26, 0
  addi x18, x29, 0
  jal x1, modload

  li x8, 2
  li x9, 3

  /* Copy p into the modulus location in DMEM[dptr_n]. */
  addi x12, x26, 0
  addi x13, x28, 0
  loop x30, 2
    bn.lid  x8, 0(x12++)
    bn.sid  x8, 0(x13++)

  /* Calculate DMEM[dptr_d0] = p-1. */
  bn.lid x8, 0(x26)
  bn.subi w2, w2, 1
  bn.sid x8, 0(x26)

  /*
   * Boolean mask DMEM[dptr_d0] = (p-1) ^ m, DMEM[dptr_d1] = m.
   *
   * XXX: Does this leak?
   */
  addi x12, x26, 0
  addi x13, x27, 0
  loop x30, 6
    bn.lid  x8, 0(x12)
    bn.wsrr w3, URND
    bn.xor  w31, w31, w31 # dummy instruction
    bn.xor  w2, w2, w3
    bn.sid  x8, 0(x12++)
    bn.sid  x9,  0(x13++)

  /* Calculate new random witness DMEM[dptr_r0] = a. */
  addi x12, x23, 0
  loop x30, 2
    bn.wsrr w2, URND
    bn.sid  x8, 0(x12++)

  jal x1, modexp

  /* If the result is not 1, then p is not a prime number. */
  addi x16, x23, 0
  jal x1, is_1

  bn.cmp   w24, w31, FG0
  csrrs    x2, FG0, x0
  andi     x2, x2, 8
  bne      x2, x0, _check_primality_fail

/**********************************************************
 * End Fermat Test
 **********************************************************/

  li x8, 2
  li x9, 3

  /*
   * Calculate (p-1)/2.
   *
   * XXX: Should be possible shift and remask at the same time.
   */
  addi x13, x26, 0
  addi x14, x27, 0
  loop x31, 8
    bn.lid  x8, 0(x13)
    bn.lid  x9, 32(x13)
    bn.rshi w2, w3, w2 >> 1
    bn.sid  x8, 0(x13++)
    bn.lid  x8, 0(x14)
    bn.lid  x9, 32(x14)
    bn.rshi w2, w3, w2 >> 1
    bn.sid  x8,  0(x14++)

  /* Last iteration is special. */
  bn.lid  x8, 0(x13)
  bn.rshi w2, w31, w2 >> 1
  bn.sid  x8, 0(x13++)
  bn.lid  x8, 0(x14)
  bn.rshi w2, w31, w2 >> 1
  bn.sid  x8,  0(x14++)

/**********************************************************
 * Begin Miller-Rabin Test
 **********************************************************/

  /*
   * Since we assume that p mod 4 == 3, the Miller-Rabin Test simplifies to
   * simply calculating a^((p-1)/2) mod p. For some random witness a.
   */

  /* Calculate the required number of iterations. */
  li      x10, 4
  bne     x10, x30, _check_num_rounds_done
  addi    x10, x10, 1
  addi    x10, x0, 5

_check_num_rounds_done:

  loop x10, 27
    /* Calculate new random witness DMEM[dptr_r0] = a. */
    addi x12, x23, 0
    loop x30, 2
      bn.wsrr w2, URND
      bn.sid  x8, 0(x12++)

    jal x1, modexp

    /*
     * If a^((p-1)/2) mod p != 1 or  a^((p-1)/2) mod p != p-1, then p is not
     * a prime number.
     */
    addi x16, x23, 0
    jal x1, is_1

    bn.mov w25, w24

    jal x1, is_pminus1
    bn.or w24, w24, w25

    bn.cmp w24, w31, FG0
    csrrs  x2, FG0, x0
    andi   x2, x2, 8
    bne    x2, x0, _check_primality_fail

    /*
     * Remask (p-1)/2
     *
     * XXX: This should not leak?
     */
    li   x8, 2
    li   x9, 3
    addi x12, x26, 0
    addi x13, x27, 0
    loop x30, 7
      bn.lid  x8, 0(x12)
      bn.lid  x9, 0(x13)
      bn.wsrr w4, URND
      bn.xor  w2, w2, w4
      bn.sid  x8, 0(x12++)
      bn.xor  w3, w3, w4
      bn.sid  x9,  0(x13++)
    nop

/**********************************************************
 * End Miller-Rabin Test
 **********************************************************/

  /* p is prime with overwhelming probability. */
  ret

 _check_primality_fail:
  /* p is a composite number. */
  bn.sub  w24, w24, w24
  ret

/**
 * Check whether the multi-word value x is equal to 1.
 *
 * Returns the all-1 value (2^256-1) in w24 if x == 1 else 0.
 *
 * @param[in]  x16: dptr_x, pointer to input buffer x in dmem
 * @param[in]  x31: n-1, number of limbs for all bignums (wlen / 256; n <= 16)
 * @param[in]  w31: all-zero
 * @param[out] w24: result, 2^256-1 or 0
 *
 * Clobbered Registers: x8, x9, w2
 * Clobbered Flag Groups: FG0
 */
is_1:
  li x8, 2
  addi x9, x16, 0

  bn.sub   w24, w24, w24
  bn.not   w24, w24

  /* Check whether the LSB word is equal to 1. */
  bn.lid  x8, 0(x9++)
  bn.subi w2, w2, 1
  bn.cmp  w2, w31, FG0
  bn.sel  w24, w24, w31, FG0.Z

  /* Loop over the remaining words and check whether they are 0. */
  loop     x31, 3
    bn.lid   x8, 0(x9++)
    bn.cmp   w2, w31, FG0
    bn.sel   w24, w24, w31, FG0.Z

  ret

/**
 * Check whether the x is equal to the modulus p-1.
 *
 * Returns the all-1 value (2^256-1) in w24 if x == (p-1) else 0.
 * Note that p-1 is assumed to an even number.
 *
 * @param[in]  x16: dptr_x, pointer to input buffer x in dmem
 * @param[in]  x28: modulus p
 * @param[in]  x30: n, number of limbs for all bignums (wlen / 256; n <= 16)
 * @param[out] w24: result, 2^256-1 or 0
 *
 * Clobbered Registers: x8, x9, x10, x11, w2, w3
 * Clobbered Flag Groups: FG00
 */
is_pminus1:
  li x8, 2
  li x9, 3
  addi x10, x16, 0
  addi x11, x28, 0

  bn.sub   w24, w24, w24
  bn.not   w24, w24

  /*
   * Check the equality of the LSB word. Since p is an odd number we can simply
   * subtract 1 from the LSB without caring about any borrow words.
   */
  bn.lid  x8, 0(x10++)
  bn.lid  x9, 0(x11++)
  bn.subi w3, w3, 1
  bn.cmp  w2, w3, FG0
  bn.sel  w24, w24, w31, FG0.Z

  /* Check the remaining words for equality. */
  loop     x31, 4
    bn.lid x8, 0(x10++)
    bn.lid x9, 0(x11++)
    bn.cmp w2, w3, FG0
    bn.sel w24, w24, w31, FG0.Z

  ret

/**
 * Check if a large number is relatively prime to 65537 (aka F4).
 *
 * Returns a nonzero value if GCD(x,65537) == 1, and 0 otherwise
 *
 * A naive implementation would simply check if GCD(x, F4) == 1, However, we
 * can simplify the check for relative primality using a few helpful facts
 * about F4 specifically:
 *   1. It is prime.
 *   2. It has the special form (2^16 + 1).
 *
 * Because F4 is prime, checking if a number x is relatively prime to F4 means
 * simply checking if x is a direct multiple of F4; if (x % F4) != 0, then x is
 * relatively prime to F4. This means that instead of computing GCD, we can use
 * basic modular arithmetic.
 *
 * Here, the special form of F4, fact (2), comes in handy. Since 2^32 mod F4 =
 * 1, we can use `fold_bignum` to bring the number down to 35 bits cheaply.
 *
 * Since 2^16 is equivalent to -1 modulo F4, we can express the resulting
 * number in base-2^16 and simplify as follows:
 *   x = x0 + 2^16 * x1 + 2^32 * x2
 *   x \equiv x0 + (-1) * x1 + (-1)^2 * x2
 *   x \equiv x0 - x1 + x2 (mod F4)
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x16: dptr_x, pointer to first limb of x in dmem
 * @param[in]  x30: n, number of 256-bit limbs for x
 * @param[in]  w31: all-zero
 * @param[out] w24: 2^256 if gcd(x, F4) == 1 else 0
 *
 * clobbered registers: x2, w22, w23, w25
 * clobbered flag groups: FG0
 */
relprime_f4:
  /* Load F4 into the modulus register for later.
       MOD <= 2^16 + 1 */
  bn.addi  w22, w31, 1
  bn.add   w22, w22, w22 << 16
  bn.wsrw  MOD, w22

  /* Generate a 256-bit mask.
       w24 <= 2^256 - 1 */
  bn.not   w24, w31

  /* Fold the bignum to get a 35-bit number r such that r mod F4 = x mod F4.
       w23 <= r */
  jal      x1, fold_bignum

  /* Isolate the lower 16 bits of the 35-bit working sum.
       w22 <= w23[15:0] */
  bn.and   w22, w23, w24 >> 240

  /* Add the lower 16 bits of the sum to the highest 3 bits to get a 17-bit
     result.
       w22 <= w22 + (w23 >> 32) */
  bn.add   w22, w22, w23 >> 32

  /* The sum from the previous addition is at most 2^16 - 1 + 2^3 - 1 < 2 * F4,
     so a modular addition with zero is sufficient to fully reduce.
       w22 <= w22 mod F4 */
  bn.addm  w22, w22, w31

  /* Isolate the subtraction term.
       w23 <= w23[31:16] */
  bn.rshi  w23, w23, w31 >> 32
  bn.rshi  w23, w31, w23 >> 240

  /* Final subtraction modulo F4.
       w22 <= (w22 - w23) mod F4 = x mod F4 */
  bn.subm  w22, w22, w23

  /* Return 2^256-1 if gcd(x, F4) == 1 else 0. */
  bn.xor   w25, w25, w25
  bn.not   w25, w25
  bn.cmp   w22, w31, FG0
  bn.sel   w24, w31, w25, FG0.Z
  ret

/**
 * Partially reduce a value modulo m such that 2^32 mod m == 1.
 *
 * Returns r such that r mod m = x mod m and r < 2^35.
 *
 * Can be used to speed up modular reduction on certain numbers, such as 3, 5,
 * 17, and 65537.
 *
 * Because we know 2^32 mod m is 1, it follows that in general 2^(32*k) for any
 * k are all 1 modulo m. This includes 2^256, so when we receive the input as
 * a bignum in 256-bit limbs, we can simply all the limbs together to get an
 * equivalent number modulo m:
 *  x = x[0] + 2^256 * x[1] + 2^512 * x[2] + ...
 *  x \equiv x[0] + x[1] + x[2] + ... (mod F4)
 *
 * From there, we can essentially use the same trick to bisect the number into
 * 128-bit, 64-bit, and 32-bit chunks and add these together to get an
 * equivalent number modulo m. This operation is visually sort of like folding
 * the number over itself repeatedly, which is where the function gets its
 * name.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x16: dptr_x, pointer to first limb of x in dmem
 * @param[in]  x30: plen, number of 256-bit limbs for x
 * @param[in]  w24: constant, 2^256 - 1
 * @param[in]  w31: all-zero
 * @param[out] w23: r, result
 *
 * clobbered registers: x2, w22, w23
 * clobbered flag groups: FG0
 */
fold_bignum:
  /* Initialize constants for loop. */
  li      x22, 22

  /* Copy input pointer. */
  addi    x2, x16, 0

  /* Initialize sum to zero and clear FG0.C.
       w23 <= 0
       FG0.C <= 0 */
  bn.addi  w23, w31, 0

  /* Iterate through the limbs of x and add them together.

     Loop invariants for iteration i (i=0..n-1):
       x2 = dptr_x + i*32
       x22 = 22
       (w23 + FG0.C) \equiv x[0] + x[1] + ... + x[i-1] (mod m)
   */
  loop    x30, 2
    /* Load the next limb.
         w22 <= x[i] */
    bn.lid   x22, 0(x2++)

    /* Accumulate the new limb, incorporating the carry bit from the previous
       round if there was one (this works because 2^256 \equiv 1 mod m).
         w23 <= (w23 + x[i] + FG0.C) mod 2^256
         FG0.C <= (w23 + x[i] + FG0.C) / 2^256 */
    bn.addc  w23, w23, w22

  /* Isolate the lower 128 bits of the sum.
       w22 <= w23[127:0] */
  bn.and   w22, w23, w24 >> 128

  /* Add the two 128-bit halves of the sum, plus the carry from the last round
     of the sum computation. The sum is now up to 129 bits.
       w23 <= (w22 + (w23 >> 128) + FG0.C) */
  bn.addc  w23, w22, w23 >> 128

  /* Isolate the lower 64 bits of the sum.
       w22 <= w23[63:0] */
  bn.and   w22, w23, w24 >> 192

  /* Add the two halves of the sum (technically 64 and 65 bits). A carry was
     not possible in the previous addition since the value is too small. The
     value is now up to 66 bits.
       w23 <= (w22 + (w23 >> 64)) */
  bn.add   w23, w22, w23 >> 64

  /* Isolate the lower 32 bits of the sum.
       w22 <= w23[31:0] */
  bn.and   w22, w23, w24 >> 224

  /* Add the two halves of the sum (technically 32 and 34 bits). A carry was
     not possible in the previous addition since the value is too small.
       w23 <= (w22 + (w23 >> 32)) */
  bn.add   w23, w22, w23 >> 32

  ret
