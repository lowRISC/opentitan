/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Exposed for testing purposes only. */
.globl relprime_f4

/**
 * Check if a large number is relatively prime to 65537 (aka F4).
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
 * Here, the special form of F4, fact (2), comes in handy. Note that 2^16 is
 * equivalent to -1 modulo F4. So if we express a number x in base-2^16, we can
 * simplify as
 * follows:
 *   x = x0 + 2^16 * x1 + 2^32 * x2 + 2^48 * x3 + ...
 *   x \equiv x0 + (-1) * x1 + (-1)^2 * x2 + (-1)^3 * x3 + ... (mod F4)
 *   x \equiv x0 - x1 + x2 - x3 + ... (mod F4)
 *
 * An additionally helpful observation based on fact (2) is that 2^32, 2^64,
 * and in general 2^(32*k) for any k are all 1 modulo F4. This includes 2^256,
 * so when we receive the input as a bignum in 256-bit limbs, we can simply
 * all the limbs together to get an equivalent number modulo F4:
 *  x = x[0] + 2^256 * x[1] + 2^512 * x[2] + ...
 *  x \equiv x[0] + x[1] + x[2] + ... (mod F4)
 *
 * From there, we can essentially use the same trick to bisect the number into
 * 128-bit, 64-bit, and 32-bit chunks and add these together to get an
 * equivalent number modulo F4. For the final 16-bit chunks, we need to
 * subtract because 2^16 mod F4 = -1 rather than 1.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x16: dptr_x, pointer to first limb of x in dmem
 * @param[in]  x30: n, number of 256-bit limbs for x
 * @param[in]  w31: all-zero
 * @param[out] w22: result, 0 only if x is not relatively prime to F4
 *
 * clobbered registers: x2, w22, w23
 * clobbered flag groups: FG0
 */
relprime_f4:
  /* Load F4 into the modulus register for later.
       MOD <= 2^16 + 1 */
  bn.addi  w22, w31, 1
  bn.add   w22, w22, w22 << 16
  bn.wsrw  0x0, w22

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
       (w23 + FG0.C) \equiv x[0] + x[1] + ... + x[i-1] (mod F4)
   */
  loop    x30, 2
    /* Load the next limb.
         w22 <= x[i] */
    bn.lid   x22, 0(x2++)

    /* Accumulate the new limb, incorporating the carry bit from the previous
       round if there was one (this works because 2^256 \equiv 1 mod F4).
         w23 <= (w23 + x[i] + FG0.C) mod 2^256
         FG0.C <= (w23 + x[i] + FG0.C) / 2^256 */
    bn.addc  w23, w23, w22

  /* Isolate the lower 128 bits of the sum.
       w22 <= w23[127:0] */
  bn.rshi  w22, w23, w31 >> 128
  bn.rshi  w22, w31, w22 >> 128

  /* Add the two 128-bit halves of the sum, plus the carry from the last round
     of the sum computation. The sum is now up to 129 bits.
       w23 <= (w22 + (w23 >> 128) + FG0.C) */
  bn.addc  w23, w22, w23 >> 128

  /* Isolate the lower 64 bits of the sum.
       w22 <= w23[63:0] */
  bn.rshi  w22, w23, w31 >> 64
  bn.rshi  w22, w31, w22 >> 192

  /* Add the two halves of the sum (technically 64 and 65 bits). A carry was
     not possible in the previous addition since the value is too small. The
     value is now up to 66 bits.
       w23 <= (w22 + (w23 >> 64)) */
  bn.add   w23, w22, w23 >> 64

  /* Isolate the lower 32 bits of the sum.
       w22 <= w23[31:0] */
  bn.rshi  w22, w23, w31 >> 32
  bn.rshi  w22, w31, w22 >> 224

  /* Add the two halves of the sum (technically 32 and 34 bits). A carry was
     not possible in the previous addition since the value is too small.
       w23 <= (w22 + (w23 >> 32)) */
  bn.add   w23, w22, w23 >> 32

  /* Note: At this point, we're down to the last few terms:
       x \equiv (w23[15:0] - w23[31:16] + w23[34:32]) mod F4 */

  /* Isolate the lower 16 bits of the 35-bit working sum.
       w22 <= w23[15:0] */
  bn.rshi  w22, w23, w31 >> 16
  bn.rshi  w22, w31, w22 >> 240

  /* Add the lower 16 bits of the sum to the highest 3 bits to get a 17-bit
     result.
       w22 <= w22 + (w23 >> 32) */
  bn.add   w22, w22, w23 >> 32

  /* The sum from the previous addition is < 2 * F4, so a modular addition with
     zero is sufficient to fully reduce.
       w22 <= w22 mod F4 */
  bn.addm  w22, w22, w31

  /* Isolate the subtraction term.
       w23 <= w23[31:16] */
  bn.rshi  w23, w23, w31 >> 32
  bn.rshi  w23, w31, w23 >> 240

  /* Final subtraction modulo F4.
       w22 <= (w22 - w23) mod F4 = x mod F4 */
  bn.subm  w22, w22, w23

  ret
