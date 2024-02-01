/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl bignum_mul

/**
 * Compute the product of two bignums.
 *
 * Returns c = a * b.
 *
 * The basic algorithm here is a textbook multi-limb multiplication:
 *   out = 0
 *   for i=0..n-1:
 *     for j=0..n-1:
 *       out += (a[i]*b[j]) << (256*(i+j))
 *
 * When adding partial products, we just iterate over the whole remaining
 * output buffer to propagate carries. Specialized implementations can do
 * better here by using fast "carry chains" to add specific partial products in
 * sequence, so specialized implementations are recommended over this approach
 * for performance-critical code.
 *
 * This routine runs in constant-time relative to the input *values*, but the
 * number of limbs is considered non-secret.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x10: dptr_a, dmem address of first operand (n limbs)
 * @param[in]  x11: dptr_b, dmem address of second operand (n limbs)
 * @param[in]  x12: dptr_c, dmem address of buffer for result (n*2 limbs)
 * @param[in]  x30: number of 256-bit limbs for each operand
 * @param[in]  w31: all-zero
 * @param[out] dmem[x12..x12+(n*2*32)]: result, a*b
 *
 * clobbered registers: x2 to x8, x20 to x23, w20 to w23
 * clobbered flag groups: FG0
 */
bignum_mul:
  /* Zeroize output buffer.
       dmem[dptr_c..dptr_c+(n*2*32)] <= 0 */
  add      x2, x30, x30
  li       x3, 31
  addi     x4, x12, 0
  loop     x2, 1
    bn.sid   x3, 0(x4++)

  /* Copy bignum pointers.
       x2 <= dptr_a
       x4 <= dptr_c */
  addi     x2, x10, 0
  addi     x4, x12, 0

  /* Load constants to use as wide-register pointers. */
  li       x20, 20
  li       x21, 21
  li       x22, 22
  li       x23, 23

  /* x6 <= 2*n */
  add      x6, x30, x30

  /* Clear flags. */
  bn.sub   w31, w31, w31

  /* Loop through the limbs of a.

     Loop invariants for iteration i (i=0..n-1):
       x2 = dptr_a + i*32
       x4 = dptr_c + i*32
       x6 = n-i
       dmem[dptr_c..dptr_c+(n*32)] = (a mod 2^(256*i)) * b
   */
  loop     x30, 22
    /* w20 <= a[i] */
    bn.lid   x20, 0(x2++)

    /* Reset the pointer to b.
         x3 <= dptr_b */
    addi     x3, x11, 0

    /* Decrement high-limb counter.
         x6 <= x6 - 1 = 2*n-1-i */
    addi     x8, x0, 1
    sub      x6, x6, x8

    /* Copy the pointer to c[i].
         x5 <= dptr_c + i*32 */
    addi     x5, x4, 0

    /* Copy the high-limb counter.
         x7 <= 2*n-1-i */
    addi     x7, x6, 0

    /* Loop through the limbs of b.

       Loop invariants for iteration j (j=0..n-1):
         w20 = a[i]
         x3 = dptr_b + i*32
         x5 = dptr_c + (i+j)*32
         x7 = 2*n-1-(i+j)
         dmem[dptr_c..dptr_c+(n*32)] + FG0.C*2^(256*(i+j+1)) =
           (a mod 2^(256*i)) * b + a[i] * (b mod 2^(256*j))
    */
    loop     x30, 13
      /* w22, w23 <= w20*b[j] = a[i]*b[j] */
      bn.lid    x21, 0(x3++)
      jal       x1, mul256_w20xw21
      /* out[i+j], FG0.C <= w22 + out[i+j] */
      bn.lid    x21, 0(x5)
      bn.add    w22, w22, w21
      bn.sid    x22, 0(x5++)
      /* x8 <= x5 = dptr_c + (i+j+1)*32 */
      addi      x8, x5, 0
      /* Propagate the carry through the remaining output limbs. */
      loop      x7, 4
        bn.lid    x21, 0(x8)
        bn.addc   w21, w21, w23
        bn.sid    x21, 0(x8++)
        bn.mov    w23, w31
      /* x7 <= x7 - 1 = 2*n-1-(i+j+1)*/
      addi      x8, x0, 1
      sub       x7, x7, x8

    /* Increment the pointer to c[i] for the next round.
         x4 <= x4 + 32 = dptr_c + (i+1)*32 */
    addi     x5, x0, 32
    add      x4, x4, x5

  ret

/**
 * Unrolled 512=256x256 bit multiplication.
 *
 * Returns c = a * b.
 *
 * Flags: No flags are set in this subroutine.
 *
 * @param[in] w20: a, first operand
 * @param[in] w21: b, second operand
 * @param[out] [w22, w23]: c, result
 *
 * clobbered registers: w22, w23
 * clobbered flag groups: None
 */
mul256_w20xw21:
  bn.mulqacc.z          w20.0, w21.0,  0
  bn.mulqacc            w20.1, w21.0, 64
  bn.mulqacc.so  w22.L, w20.0, w21.1, 64
  bn.mulqacc            w20.2, w21.0,  0
  bn.mulqacc            w20.1, w21.1,  0
  bn.mulqacc            w20.0, w21.2,  0
  bn.mulqacc            w20.3, w21.0, 64
  bn.mulqacc            w20.2, w21.1, 64
  bn.mulqacc            w20.1, w21.2, 64
  bn.mulqacc.so  w22.U, w20.0, w21.3, 64
  bn.mulqacc            w20.3, w21.1,  0
  bn.mulqacc            w20.2, w21.2,  0
  bn.mulqacc            w20.1, w21.3,  0
  bn.mulqacc            w20.3, w21.2, 64
  bn.mulqacc.so  w23.L, w20.2, w21.3, 64
  bn.mulqacc.so  w23.U, w20.3, w21.3,  0
  ret
