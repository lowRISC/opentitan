/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl lcm

/**
 * Compute the LCM of two bignums.
 *
 * Returns c = LCM(a, b).
 *
 * To compute the LCM, we compute b * (a / GCD(a, b)). Calling this function
 * clobbers the first operand (a) in DMEM.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x10: dptr_a, dmem address of first operand (n limbs)
 * @param[in]  x11: dptr_b, dmem address of second operand (n limbs)
 * @param[in]  x12: dptr_c, dmem address of buffer for result (n*2 limbs)
 * @param[in]  x30: number of 256-bit limbs for each operand
 * @param[in]  w31: all-zero
 * @param[out] dmem[dptr_c..dptr_c+(n*2*32)]: result, LCM(a,b)
 *
 * clobbered registers: x2 to x8, x20 to x25, w20 to w25
 * clobbered flag groups: FG0
 */
lcm:
  /* Initialize wide-register pointers. */
  li       x20, 20
  li       x21, 21

  /* Copy both operands to the result buffer (GCD overwrites them).
       dmem[dptr_c..dptr_c+(n*32)] <= a
       dmem[dptr_c+(n*32)..dptr_c+(2*n*32)] <= b */
  addi     x2, x10, 0
  addi     x3, x12, 0
  loop     x30, 2
    bn.lid   x20, 0(x2++)
    bn.sid   x20, 0(x3++)
  addi     x2, x11, 0
  loop     x30, 2
    bn.lid   x20, 0(x2++)
    bn.sid   x20, 0(x3++)

  /* dmem[x11..x11+(n*32)] <= GCD(dmem[x10..x10+(n*32)], dmem[x11..x11+(n*32)])
                            = GCD(a, b) */
  jal        x1, gcd

  /* Copy the first operand back into its original buffer.
       dmem[dptr_a..dptr_a+(n*32)] <= dmem[dptr_c..dptr_c+(n*32)] */
  addi     x2, x12, 0
  addi     x3, x10, 0
  loop     x30, 2
    bn.lid   x20, 0(x2++)
    bn.sid   x20, 0(x3++)

  /* dmem[x12..x12+(n*32)] <= floor(dmem[x10..x10+(n*32)] / dmem[x11..x11+(n*32)])
                            = floor(a / GCD(a, b)) */
  jal        x1, div

  /* Copy the quotient into the buffer that originally held the first operand.
       dmem[x10..x10+(n*32)] <= dmem[x12..x12+(n*32)] = floor(a / GCD(a, b)) */
  addi     x2, x12, 0
  addi     x3, x10, 0
  loop     x30, 2
    bn.lid   x20, 0(x2++)
    bn.sid   x20, 0(x3++)

  /* Copy the second operand back into its original buffer.
       dmem[dptr_b..dptr_b+(n*32)] <= dmem[dptr_c+(n*32)..dptr_c+(2n*32)] = b */
  addi     x3, x11, 0
  loop     x30, 2
    bn.lid   x20, 0(x2++)
    bn.sid   x20, 0(x3++)

  /* dmem[x12..x12+(n*2*32) <= dmem[x10..x10+(n*32)] * dmem[x11..x11+(n*32)]
                             = floor(a / GCD(a,b)) * b = LCM(a,b) */
  jal      x1, bignum_mul

  ret
