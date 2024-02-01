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
