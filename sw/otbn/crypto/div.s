/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl div

/**
 * Shift a bignum one bit to the right.
 *
 * Returns a' = lsb(b) || a >> 1.
 *
 * This is a customized helper function for `div`. Modifies the input in-place.
 * This routine runs in constant time.
 *
 * Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]      x3: dptr_a, pointer to input a in DMEM
 * @param[in]     x23: 23, constant
 * @param[in]     x24: 24, constant
 * @param[in]     x30: n, number of 256-bit limbs
 * @param[in]     w23: b, input whose LSB will be the new MSB of a
 * @param[in]     w31: all-zero
 * @param[out] dmem[dptr_a..dptr_a+n*32]: a', result
 *
 * clobbered registers: x2, x3, w23, w24
 * clobbered flag groups: none
 */
bignum_rshift1:
   /* Get a pointer to the end of the input.
        x3 <= x3 + x30 << 5 = dptr_a + n*32 */
   slli      x2, x30, 5
   add       x3, x3, x2

   /* x2 <= 32 */
   li        x2, 32

   /* Loop invariants for iteration i:
        x2 = 32
        x3 = dptr_a + ((n-i) * 32)
        w23 = if i == 0 then b else a[n-i] */
   loop      x30, 5
     /* x3 <= x3 - 32 = dptr_a + (n-1-i)*32 */
     sub     x3, x3, x2
     /* w24 <= dmem[x3] = a[n-1-i] */
     bn.lid    x24, 0(x3)
     /* w23 <= (w23 || w24) >> 1) = a'[n-1-i] */
     bn.rshi   w23, w23, w24 >> 1
     /* dmem[x3] <= w23 = a'[n-1-i] */
     bn.sid    x23, 0(x3)
     /* w23 <= w24 */
     bn.mov    w23, w24

  ret

/**
 * Shift a bignum 256 bits to the left in memory.
 *
 * Returns a' = a << 256.
 *
 * This is a customized helper function for `div`. Modifies the input in-place,
 * This routine runs in constant time.
 *
 * The new highest limb is stored in a register, since we assume there is no
 * extra DMEM space allocated for it.
 *
 * Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]      x3: dptr_a, pointer to input a in DMEM
 * @param[in]     x23: 23, constant
 * @param[in]     x24: 24, constant
 * @param[in]     x30: n, number of 256-bit limbs
 * @param[in]     w31: all-zero
 * @param[out]    w23: highest limb of original a value
 *
 * clobbered registers: x3, w23, w24
 * clobbered flag groups: none
 */
bignum_lshift256:
  /* Loop invariants for iteration i:
       x3 = dptr_a + i*32
       w23 = if i == 0 then 0 else a[i-1]
       dmem[dptr_a..dptr_a+i*32] = (a << 256) mod 2^(i*32) */
  bn.mov    w23, w31
  loop      x30, 3
    /* w24 <= a[i] */
    bn.lid    x24, 0(x3)
    /* a[i] <= w23 = a[i-1] */
    bn.sid    x23, 0(x3++)
    /* w23 <= w24 */
    bn.mov    w23, w24

  ret

/**
 * Conditionally subtract a shifted bignum from another bignum.
 *
 * Returns r' = if (r > y << (i*256)) then (r - y << (i*256)) else r.
 *
 * Updates r in-place.
 *
 * This is a specialized helper function for `div`. It expects its inputs in
 * specific forms that come from the constraints of that function. In
 * particular, the second operand y has n+1 limbs, one extra compared to r,
 * with the uppermost stored in a register.
 *
 * For the first i limbs, the shifted y is 0 so r will always remain unchanged.
 * For the next (n-i) iterations, we subtract corresponding limbs.  For the
 * last i iterations, we would need to subtract the remaining limbs of y from
 * 0; however, since we would never use this result if it were nonzero, we
 * simply compute the borrow rather than a full subtraction. Finally, we check
 * the borrow at the end of the computation and, if the subtraction
 * underflowed, we add back the limbs of y that we subtracted to leave r
 * unchanged.
 *
 * Algorithmically, this looks something like:
 *   borrow = 0
 *   for k=0..n-1:
 *     if k+i < n:
 *       r[k+i], borrow = subb(r[k+i], y[k], borrow)
 *     else:
 *       borrow &= (y[k] == 0)
 *   mask = borrow ? 2^256 - 1 : 0
 *   carry = 0
 *   for k=0..n-i-1:
 *     r[k+i], carry = addc(r[k+i], y[k] & mask, carry)
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]    x8: i, number of limbs to shift y (i < n)
 * @param[in]   x10: dptr_r, pointer to first operand r in dmem (n*32 bytes)
 * @param[in]   x11: dptr_y, pointer to second operand y in dmem (n*32 bytes)
 * @param[in]   x24: 24, constant
 * @param[in]   x25: 25, constant
 * @param[in]   x30: n, number of 256-bit limbs for operands r and y
 * @param[in]   w27: y_upper, highest limb of y
 * @param[in]   w31: all-zero
 * @param[out]  w23: mask, 0 if the subtraction was performed and -1 otherwise
 * @param[out] dmem[dptr_r..dptr_r+n*32]: result r'
 *
 * clobbered registers: x2 to x5, w23 to w25
 * clobbered flag groups: FG0
 */
cond_sub_shifted:
  /* x3 <= x8 << 5 = i*32 */
  slli     x3, x8, 5

  /* Get a pointer to the ith limb of r.
       x2 <= x10 + x3 = dptr_r + i*32 */
  add      x2, x3, x10

  /* Copy pointer to second operand.
       x4 <= x11 = dptr_y */
  addi      x4, x11, 0

  /* Initialize counter.
       x5 <= x8 = i */
  addi     x5, x8, 0

  /* Clear flags. */
  bn.add    w31, w31, w31

  /* First loop; subtract corresponding limbs.

     Loop invariants for iteration k (k=0..n-1):
       x2 = dptr_r + x5*32
       x4 = dptr_y + k*32
       x5 = (k + i <= n) ? k + i : n
       x30 = n
       FG0.C = r mod 2^(k *256)) < (y << (i*256)) mod 2^(k*256)
  */
  loop    x30, 9
    /* Load the next limb of the shifted y.
         w24 <= y[k] */
    bn.lid    x24, 0(x4++)

    /* Check if k+i == n (x5 == x30) and skip to the only-borrow case if so. This
       branch only depends on limb indices, so it does not break constant-time
       properties. */
    beq       x5, x30, _cond_sub_shifted_high_limb

    /* r[k+i], FG0.C <= r[k+i] - y[k] - FG0.C */
    bn.lid    x25, 0(x2)
    bn.subb   w25, w25, w24
    bn.sid    x25, 0(x2++)

    /* Increment counter.
         x5 <= x5 + 1 = k + i + 1 */
    addi      x5, x5, 1

    /* Unconditionally branch to the end of the loop. */
    jal       x0, _cond_sub_shifted_loop_end

    _cond_sub_shifted_high_limb:
    /* FG0.C <= 0 < (y[k] + FG0.C) */
    bn.cmpb   w31, w24

    _cond_sub_shifted_loop_end:
    nop

  /* Compare with the last limb of y (stored in a register).
       FG0.C <= 0 < (y_upper + FG0.C) */
  bn.cmpb   w31, w27

  /* Compute a mask based on the final borrow.
       w23 <= FG0.C ? 2^256 - 1 : 0 = mask */
  bn.subb   w23, w31, w31

  /* Get a pointer to the ith limb of r again.
       x2 <= x10 + x3 = dptr_r + i*32 */
  add      x2, x3, x10

  /* Calculate the number of iterations for the copy loop. Since i < n, this
     will always be nonzero.
       x4 <= x30 - x8 = n - i */
  sub       x5, x30, x8

  /* Clear flags. */
  bn.add    w31, w31, w31

  /* Add back the low limbs of y if there was underflow. */
  addi      x3, x11, 0
  loop      x5, 5
    /* w24 <= r[k+i] */
    bn.lid    x24, 0(x2)
    /* w25 <= y[k] */
    bn.lid    x25, 0(x3++)
    /* w25 <= y[k] & mask */
    bn.and    w25, w25, w23
    /* w24 <= r[k+i] + (y[k] & mask) */
    bn.addc   w24, w24, w25
    /* r[k+i] <= w24 */
    bn.sid    x24, 0(x2++)

  ret

/**
 * Constant-time floor division of arbitrarily large numbers.
 *
 * Returns q = floor(x / y).
 *
 * This routine performs binary long division. Faster algorithms certainly
 * exist, but this one is comparatively simple to write and to make
 * constant-time. In pseudocode:
 *   q = 0 // quotient
 *   r = x // remainder
 *   for i=nbits(x)..0:
 *     q <<= 1
 *     if r >= (y << i)
 *       r -= (y << i)
 *       q += 1
 *
 * The general algorithmic approach is inspired by BoringSSL's implementation:
 *   https://boringssl.googlesource.com/boringssl/+/1b2b7b2e70ce5ff50df917ee7745403d824155c5/crypto/fipsmodule/bn/div.c#457
 *
 * None of the caller-provided buffers may overlap in DMEM. The buffer for the
 * numerator will be overwritten with the remainder, while the denominator will
 * be preserved as-is.
 *
 * Flags have no meaning outside the scope of this subroutine.
 *
 * @param[in] x10: dptr_x, pointer to numerator x in dmem
 * @param[in] x11: dptr_y, pointer to denominator y in dmem
 * @param[in] x12: dptr_q, pointer to buffer for quotient q in dmem
 * @param[in] x30: n, number of 256-bit limbs for inputs x and y
 * @param[in] w31: all-zero
 * @param[out] dmem[dptr_q..dptr_q+n*32]: q, quotient
 * @param[out] dmem[dptr_x..dptr_x+n*32]: r, remainder
 *
 * clobbered registers: x2 to x5, x8, x23 to x25, w23 to w27
 * clobbered flag groups: FG0
 */
div:
  /* Initialize quotient to zero.
       dmem[dptr_q..dptr_q+n*32] = 0  */
  addi      x2, x12, 0
  li        x3, 31
  loop      x30, 1
    bn.sid    x3, 0(x2++)

  /* Initialize loop counter.
       x8 <= x30 = n */
  addi      x8, x30, 0

  /* Initialize constants for loop.
       x23 = 23
       x24 = 24
       x25 = 25
       x26 = 26 */
  li        x23, 23
  li        x24, 24
  li        x25, 25
  li        x26, 26

  /* Main loop. This loop iterates through limbs of the quotient, and then the
     inner loop iterates through bits of each limb.

     Loop invariants for iteration i of outer loop (i=n-1..0):
       x8 = i + 1
       x23 = 23
       x24 = 24
       x25 = 25
       x25 = 26
       dmem[dptr_q..(i+1)*32] = 0
       q * y + r = x
       r < y << ((i+1)*256)
  */
  loop      x30, 17
    /* Decrement counter.
         x8 <= x8 - 1 = i */
    addi      x5, x0, 1
    sub       x8, x8, x5

    /* Initialize the next limb of the quotient to 0.
         w26 <= 0 */
    bn.mov    w26, w31

    /* Shift the denominator a full limb to the left. As we iterate through
       bits, we will shift it right one bit at a time.
         w27 <= y[n-1]
         dmem[dptr_y..dptr_y+n*32] <= (y << 256) mod 2^(n*256)  */
    addi      x3, x11, 0
    jal       x1, bignum_lshift256
    bn.mov    w27, w23

    /* Inner loop. Iterates through bits in this limb of quotient, most
       significant bit first. At each iteration, we compute bit (i*256+j) of
       the quotient by checking if r >= (y << (i*256+j)). If so, we subtract
       this shifted denominator from the remainder and add a 1 at that position
       in the quotient.

       Loop invariants for iteration j of inner loop (j=255..0):
         x8 = i
         x23 = 23
         x24 = 24
         x25 = 25
         r = dmem[dptr_x..dptr_x+n*32]
         q = dmem[dptr_q..dptr_q+n*32] | (w26 << (256*i+j+1))
         y << (j + 1) = w27 || dmem[dptr_y..dptr_y+n*32]
         q * y + r = x
         r < y << (i*256 + j + 1)
    */
    loopi    256, 7
      /* Shift denominator one bit to the right.
          dmem[dptr_y..dptr_y+n*32] <= lsb(w27) || dmem[dptr_y..dptr_y+n*32] >> 1
          w27 <= w27 >> 1 */
      addi      x3, x11, 0
      bn.mov    w23, w27
      jal       x1, bignum_rshift1
      bn.rshi   w27, w31, w27 >> 1

      /* Conditional subtraction.
           dmem[dptr_x..dptr_x+n*32] <= r mod (y << (i*256+j))
           w23 <= 0 if there was a subtraction, otherwise 2^256-1 */
      jal         x1, cond_sub_shifted

      /* Invert the mask.
           w23 <= 2^256 - 1 if there was a subtraction, otherwise 0 */
      bn.not      w23, w23

      /* Update current limb of quotient.
           w26 <= w26 << 1 | msb(w23)  */
      bn.rshi     w26, w26, w23 >> 255

    /* Store the now-complete limb of the quotient.
         dmem[dptr_q+i*32] <= w26 */
    slli        x5, x8, 5
    add         x5, x5, x12
    bn.sid      x26, 0(x5)

  ret
