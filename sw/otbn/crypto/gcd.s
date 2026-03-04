/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Constant-time conditional subtraction.
 *
 * Returns a' = if FG1.L then (a - b) else a.
 *
 * This is a specialized helper function for the GCD computation. Modifies the
 * input a in-place.
 *
 * Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]    x3: dptr_a, pointer to input a in DMEM
 * @param[in]    x4: dptr_b, pointer to input b in DMEM
 * @param[in]   x23: 23, constant
 * @param[in]   x24: 24, constant
 * @param[in]   x30: n, number of 256-bit limbs for inputs a and b
 * @param[in]   w31: all-zero
 * @param[in] FG1.L: selection flag
 * @param[out] dmem[dptr_a:dptr_a+n*32]: a', result
 *
 * clobbered registers: x3, x4, x5, w23, w24
 * clobbered flag groups: FG0
 */
gcd_cond_sub:
  /* Clear flags. */
  bn.add    w31, w31, w31

  /* Loop through each limb. */
  loop      x30, 5
    /* w23 <= dmem[x3] = a[i] */
    bn.lid    x23, 0(x3)
    /* w24 <= dmem[x4] = b[i] */
    bn.lid    x24, 0(x4++)
    /* w24 <= w23 - w24 = (a - b)[i] */
    bn.subb   w24, w23, w24
    /* w24 <= FG1.L ? w24 : w23 = c[i] */
    bn.sel    w24, w24, w23, FG1.L
    /* dmem[x3] <= w24 = c[i] */
    bn.sid    x24, 0(x3++)

  ret

/**
 * Shifts input 1 bit to the right if it is even.
 *
 * Returns a' = if a[0] then a else a >> 1.
 *
 * This is a specialized helper function for the GCD computation. The input is
 * modified in-place. This routine runs in constant time.
 *
 * Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]   x3: dptr_a, pointer to input a in DMEM
 * @param[in]  x23: 23, constant
 * @param[in]  x24: 24, constant
 * @param[in]  x30: n, number of 256-bit limbs for input a
 * @param[in]   w31: all-zero
 * @param[out] dmem[dptr_a:dptr_a+n*32]: a', result
 *
 * clobbered registers: x3, x4, x22, x23, x24, w23, w24
 * clobbered flag groups: FG0
 */
gcd_cond_rshift1:
  /* x22 <= x30 - 1 = n - 1 */
  addi      x22, x0, 1
  sub       x22, x30, x22

  /* Get a pointer to the second limb of the input.
       x4 <= x3 + 32 = dptr_a + 32 */
  addi      x4, x3, 32

  /* w23 <= dmem[x3] = a[255:0] */
  bn.lid    x23, 0(x3)

  /* FG0.L <= a[0] */
  bn.add    w23, w23, w31

  /* If the number of limbs is 1, skip the loop. This check is required because
     a loop with n-1=0 iterations will cause a LOOP error. */
  beq       x22, x0, _gcd_cond_rshift1_loop_end

  /* Loop through all limbs except the last. */
  loop      x22, 5
    /* w23 <= dmem[x3] = a[i] */
    bn.lid    x23, 0(x3)
    /* w24 <= dmem[x4] = a[i+1] */
    bn.lid    x24, 0(x4++)
    /* w24 <= (a >> 1)[i] */
    bn.rshi   w24, w24, w23 >> 1
    /* w24 <= FG0.L ? w23 : w24 = a'[i] */
    bn.sel    w24, w23, w24, FG0.L
    /* dmem[x3] <= w24 = a'[i] */
    bn.sid    x24, 0(x3++)

  _gcd_cond_rshift1_loop_end:

  /* Last limb is special because there's no next limb; we use 0. */
  bn.lid    x23, 0(x3)
  bn.rshi   w24, w31, w23 >> 1
  bn.sel    w24, w23, w24, FG0.L
  bn.sid    x24, 0(x3++)

  ret

/**
 * Shifts input 1 bit to the left if the counter is nonzero.
 *
 * Returns a' = if ctr > 0 then a << 1 else a.
 *
 * This is a specialized helper function for the GCD computation. The input a
 * is modified in-place. This routine runs in constant time.
 *
 * Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]   x3: dptr_a, pointer to input a in DMEM
 * @param[in]  x23: 23, constant
 * @param[in]  x24: 24, constant
 * @param[in]  x25: 25, constant
 * @param[in]  x30: n, number of 256-bit limbs for input a
 * @param[in]  w20: ctr
 * @param[in]  w31: all-zero
 * @param[out] dmem[dptr_a:dptr_a+n*32]: a', result
 *
 * clobbered registers: x3, x22, w20, w23, w24, w25
 * clobbered flag groups: FG0
 */
gcd_cond_lshift1:
  /* Check if counter is zero.
       FG0.Z <= ctr != 0 */
  bn.addi   w20, w20, 0

  /* w23 <= 0 */
  bn.mov    w23, w31

  /* Loop through remaining limbs.

     Loop invariants (i=0 to i=n-1):
       w23 = i == 0 ? 0 : a[i-1]
       x3 = dptr_a + (i * 32)
  */
  loop      x30, 5
    /* w24 <= dmem[x3] = a[i] */
    bn.lid    x24, 0(x3)
    /* w25 <= (a << 1)[i] */
    bn.rshi   w25, w24, w23 >> 255
    /* w25 <= FG0.Z ? w24 : w25 = a'[i] */
    bn.sel    w25, w24, w25, FG0.Z
    /* dmem[x3] <= w25 = a'[i] */
    bn.sid    x25, 0(x3++)
    /* w23 <= w24 = a[i] */
    bn.mov    w23, w24

  ret

/**
 * Compute the greatest common denominator of two large numbers.
 *
 * Returns g = gcd(x, y).
 *
 * This implementation is based on an implementation from BoringSSL, which is
 * in turn a constant-time version of HAC Algorithm 14.54 (binary GCD). The
 * full implementation is here:
 *   https://boringssl.googlesource.com/boringssl/+/1b2b7b2e70ce5ff50df917ee7745403d824155c5/crypto/fipsmodule/bn/gcd_extra.c#49
 *
 * In pseudocode, this algorithm is:
 *   shift = 0
 *   num_iters = nbits(x) + nbits(y)
 *   for i=0..num_iters:
 *     if x[0] & y[0]:
 *        x = (x >= y) ? x-y : x
 *        y = (x >= y) ? y : y-x
 *     if !(x[0] | y[0]):
 *        shift += 1
 *      x = x[0] ? x : x >> 1
 *      y = y[0] ? y : y >> 1
 *    y |= x
 *    return y << shift
 *
 * The final y |= x is only needed if y is zero; the algorithm guarantees that
 * x is zero at the end of the computation otherwise. This implementation skips
 * the final or, so y must not be zero.
 *
 * This routine overwrites its inputs. At the end, the buffer for x will be 0
 * and the buffer for y will hold the result.
 *
 * The number of limbs is in principle only limited by DMEM space.
 *
 * Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]     x10: dptr_x, pointer to input x in DMEM
 * @param[in]     x11: dptr_y, pointer to input y in DMEM
 * @param[in]     x30: n, number of 256-bit limbs for x, y, and g
 * @param[in]     w31: all-zero
 * @param[out] dmem[dptr_y:dptr_y+n*32]: g, result
 *
 * clobbered registers: x3, x4, x21 to x25, w20 to w25
 * clobbered flag groups: FG0, FG1
 */
.globl gcd
gcd:
  /* Initialize the shift to 0.
       w20 <= 0 = shift */
  bn.mov    w20, w31

  /* Compute the number of iterations. The inputs x and y have n * 256 bits
     each, so the sum of their number of bits is n * 2 * 256 = n << 9.
       x21 <= x30 << 9 = num_iters */
  slli      x21, x30, 9

  /* Set up constants for loop.
      x23 <= 23
      x24 <= 24
      x25 <= 25 */
  li        x23, 23
  li        x24, 24
  li        x25, 25

  /* Main loop. */
  loop      x21, 30
    /* Load the least significant limbs of x and y.
         w23 <= dmem[x10] = x[255:0]
         w24 <= dmem[x11] = y[255:0] */
    bn.lid    x23, 0(x10)
    bn.lid    x24, 0(x11)

    /* w25 <= x[255:0] & y[255:0] */
    bn.and    w25, w23, w24

    /* Clear flags. */
    bn.add    w31, w31, w31

    /* Compare x and y.
        FG0.C <= y < x = !(x >= y) */
    addi      x3, x10, 0
    addi      x4, x11, 0
    loop      x30, 3
      bn.lid    x23, 0(x3++)
      bn.lid    x24, 0(x4++)
      bn.cmpb   w23, w24

    /* Capture final borrow in a wide register.
         w22 <= FG0.C = !(x >= y) */
    bn.addc   w22, w31, w31

    /* Update FG1.L so that it is 1 if x should be updated.
         FG1.L <= (w25 & ~w22)[0] = (x[0] & y[0]) && (x >= y) */
    bn.not    w23, w22
    bn.and    w23, w23, w25, FG1

    /* dmem[dptr_x] = cond_sub(dptr_x, dptr_y) = if FG1.L then x - y else x */
    addi      x3, x10, 0
    addi      x4, x11, 0
    jal       x1, gcd_cond_sub

    /* Update FG1.L so that it is 1 if y should be updated.
         FG1.L <= (w25[0] & w22)[0] = (x[0] & y[0]) && !(x >= y) */
    bn.and    w23, w22, w25, FG1

    /* dmem[dptr_y] = cond_sub(dptr_y, dptr_x) = if FG1.L then y - x else y */
    addi      x3, x11, 0
    addi      x4, x10, 0
    jal       x1, gcd_cond_sub

    /* Reload the least significant limbs of x and y.
         w23 <= dmem[x10] = x[255:0]
         w24 <= dmem[x11] = y[255:0] */
    bn.lid    x23, 0(x10)
    bn.lid    x24, 0(x11)

    /* FG1.L = (x[0] | y[0]) */
    bn.or     w25, w23, w24, FG1

    /* Update shift.
         w20 <= FG1.L ? w20 : w20 + 1
              = if (x[0] | y[0]) then shift else shift + 1 */
    bn.addi   w25, w20, 1
    bn.sel    w20, w20, w25, FG1.L

    /* Shift x to the right by 1 if it is even.
       dmem[dptr_x] <= if x[0] then x else x >> 1 */
    addi      x3, x10, 0
    jal       x1, gcd_cond_rshift1

    /* Shift y to the right by 1 if it is even.
       dmem[dptr_y] <= if y[0] then y else y >> 1 */
    addi      x3, x11, 0
    jal       x1, gcd_cond_rshift1
    nop

  /* End of loop. At this point we are guaranteed x = 0. */

  /* Compute the maximum value of the shift. This is the number of bits in each
     input, since the gcd cannot be greater than either of its operands.
       x21 <= x30 << 8 = n * 256 */
  slli      x21, x30, 8

  /* Shift y left to obtain the final result.
       dmem[dptr_y] <= y << w20 = y << shift */
  loop      x21, 4
    /* dmem[dptr_y] <= if w20 != 0 then dmem[dptr_y] << 1 else dmem[dptr_y] */
    addi      x3, x11, 0
    jal       x1, gcd_cond_lshift1
    /* w20 <= max(0, w20 - 1) */
    bn.subi   w23, w20, 1
    bn.sel    w20, w20, w23, FG0.C

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
 * @param[in]  x31: n, number of 256-bit limbs for x
 * @param[in]  w31: all-zero
 * @param[out] w22: non-zero, if gcd(x, F4) == 1, else 0.
 *
 * clobbered registers: x2, w22, w23
 * clobbered flag groups: FG0
 */
.globl mod_f4
mod_f4:
  /* Generate a 256-bit mask.
     w24 <= 2^256 - 1 */
  bn.not w24, w31

  /* Fold the bignum to get a 35-bit number r such that r mod F4 = x mod F4.
     w23 <= r */
  jal x1, _fold_bignum

  jal x0, mod_f4_35

/**
 * Calculate x mod F4, where x is a 35-bit value.
 *
 * @param[in]  w22: x, a 35-bit value to be reduced.
 * @param[in]  w31: all-zero
 * @param[out] w23: x mod F4.
 */
.globl mod_f4_35
mod_f4_35:
  /* Load F4 into the modulus register for later.
       MOD <= 2^16 + 1 */
  bn.addi w22, w31, 1
  bn.add  w22, w22, w22 << 16
  bn.wsrw MOD, w22

  /* Isolate the lower 16 bits of the 35-bit working sum.
       w22 <= w23[15:0] */
  bn.not w24, w31
  bn.and w22, w23, w24 >> 240

  /* Add the lower 16 bits of the sum to the highest 3 bits to get a 17-bit
     result.
       w22 <= w22 + (w23 >> 32) */
  bn.add w22, w22, w23 >> 32

  /* The sum from the previous addition is at most 2^16 - 1 + 2^3 - 1 < 2 * F4,
     so a modular addition with zero is sufficient to fully reduce.
       w22 <= w22 mod F4 */
  bn.addm w22, w22, w31

  /* Isolate the subtraction term.
       w23 <= w23[31:16] */
  bn.rshi w23, w23, w31 >> 32
  bn.rshi w23, w31, w23 >> 240

  /* Final subtraction modulo F4.
       w22 <= (w22 - w23) mod F4 = x mod F4 */
  bn.subm w22, w22, w23

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
 * a bignum in 256-bit limbs, we can simply sum all the limbs together to get an
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
 * @param[in]  x31: plen, number of 256-bit limbs for x
 * @param[in]  w24: constant, 2^256 - 1
 * @param[in]  w31: all-zero
 * @param[out] w23: r, result
 *
 * clobbered registers: x2, w22, w23
 * clobbered flag groups: FG0
 */
_fold_bignum:
  /* Initialize constants for loop. */
  li x22, 22

  /* Copy input pointer. */
  addi x2, x16, 0

  /* Initialize sum to zero and clear FG0.C.
     w23 <= 0
     FG0.C <= 0 */
  bn.addi w23, w31, 0

  /* Iterate through the limbs of x and add them together.
     Loop invariants for iteration i (i=0..n-1):
       x2 = dptr_x + i*32
       x22 = 22
       (w23 + FG0.C) \equiv x[0] + x[1] + ... + x[i-1] (mod m) */
  loop x31, 2
    /* Load the next limb.
       w22 <= x[i] */
    bn.lid x22, 0(x2++)

    /* Accumulate the new limb, incorporating the carry bit from the previous
       round if there was one (this works because 2^256 \equiv 1 mod m).
         w23 <= (w23 + x[i] + FG0.C) mod 2^256
         FG0.C <= (w23 + x[i] + FG0.C) / 2^256 */
    bn.addc w23, w23, w22

  /* Isolate the lower 128 bits of the sum.
     w22 <= w23[127:0] */
  bn.and w22, w23, w24 >> 128

  /* Add the two 128-bit halves of the sum, plus the carry from the last round
     of the sum computation. The sum is now up to 129 bits.
       w23 <= (w22 + (w23 >> 128) + FG0.C) */
  bn.addc w23, w22, w23 >> 128

  /* Isolate the lower 64 bits of the sum.
       w22 <= w23[63:0] */
  bn.and w22, w23, w24 >> 192

  /* Add the two halves of the sum (technically 64 and 65 bits). A carry was
     not possible in the previous addition since the value is too small. The
     value is now up to 66 bits.
       w23 <= (w22 + (w23 >> 64)) */
  bn.add w23, w22, w23 >> 64

  /* Isolate the lower 32 bits of the sum.
     w22 <= w23[31:0] */
  bn.and w22, w23, w24 >> 224

  /* Add the two halves of the sum (technically 32 and 34 bits). A carry was
     not possible in the previous addition since the value is too small.
       w23 <= (w22 + (w23 >> 32)) */
  bn.add w23, w22, w23 >> 32

  ret
