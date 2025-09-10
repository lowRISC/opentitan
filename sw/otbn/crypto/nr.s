/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl nr_inv
.globl nr_div

/**
 * Calculate x^-1 mod 2^256, for x < x^256 and x % 2 == 1.
 *
 * This function computes the inversion of a single 256-bit word modulo 2^256
 * using the Newton-Raphson algorithm.
 *
 * The key identity is the follwing:
 *
 *   x * y = 1 mod 2^k ==> x * y * (2 - x * y) mod 2^(2 * k)
 *
 * Hence by setting k = y = 1, we can invert x in 8 iterations with 2
 * multiplications and 1 subtraction per iteration.

 * @param[in]  w20: x, an odd value to be inverted modulo 2^256
 * @param[int] w31: all-zero
 * @param[out] w21: y, the result y = x^-1 mod 2^256
 *
 * Clobbered registers: w22, w23, w24, w25, w26, w27
 * Clobbered flag groups: FG0
 */
nr_inv:

  # We compute the following algorithm:
  #
  # w21 = y = 1
  # w22 = x
  # w23 = 2
  # for i = 0 to 7 do
  #     [w27, w26] = w21 * w22 = x * y
  #     w26 = w23 - w26 = 2 - x * y
  #     [w27, w26] = w21 * 26 = x * (2 - x * y)
  #     w21 = w26
  # endfor
  # return w21

  # w21 = y = 1
  # w22 = x
  # w23 = 2
  bn.addi w21, w31, 1
  bn.mov  w22, w20
  bn.addi w23, w31, 2

  loopi 8, 8
    # x * y
    bn.mov w24, w21
    bn.mov w25, w22
    jal x1, mul256_w24xw25

    # 2 - x * y.
    bn.sub w26, w23, w26

    # x * (2 - x * y)
    bn.mov w24, w21
    bn.mov w25, w26
    jal x1, mul256_w24xw25
    bn.mov w21, w26

  ret

/**
 * Division x * y^-1 of an n-word integer x and a 256-bit integer y.
 *
 * This algorithm computes the division of x by y through multiplications.
 * Since y < 2^256, it possible complete the division by multiplying each word
 * of x by y^-1. Note that the algorithm assumes that y^-1 mod 2^256 is
 * supplied (see nr_inv on how to compute the inverse).
 *
 * The algorithm is in-place, i.e., the result overwrites DMEM[dtpr_x].
 *
 * @param[in] x16: dptr_x, DMEM address of the n-limb dividend
 * @param[in] x30: n number of limbs
 * @param[in] w20: inverted y^-1 mod 2^256
 * @param[in] w21: 256-bit divisor y
 * @param[in] w31: all-zero
 * @param[out] DMEM[dptr_x]: result x / y
 *
 * Clobbered registers: x10-x15, x31, w20-27
 * Clobbered flag groups: FG0
 */
nr_div:

  # We compute the following algorithm:
  #
  # x12 = x16 = dptr_x
  # for i = 0 to n - 1 do
  #     [w27, w26] = w20 * w22 = x[i] * y^-1
  #     DMEM[x12++] = w26 = (x[i] * y^-1) % 2^256
  #     [w27, w26] = w21 * w26 = y * ((x[i] * y^-1) % 2^256)
  #     DMEM[x12:] = DMEM[x12:] - w27 = DMEM[x12:] - (y * x[i] * y^-1) >> 2^256
  # endfor

  # Wide register and DMEM pointers.
  addi x10, x0, 22
  addi x11, x0, 26
  addi x12, x16, 0

  # Iteration counter.
  li x13, 0

  # Only iterate over the first n-1 limbs.
  addi x31, x30, -1
  loop x31, 18
    # x[i] * y^-1
    bn.lid x10, 0(x12)
    bn.mov w24, w20
    bn.mov w25, w22
    jal x1, mul256_w24xw25
    bn.sid x11, 0(x12++)

    # y * (x[i] * y^-1 % 2^256)
    bn.mov w24, w26
    bn.mov w25, w21
    jal x1, mul256_w24xw25

    # Corrective subtraction. Iterate over the remaining n-1 - i limbs and
    # subtract y * (x[i] * y^-1) >> 2^256
    addi x14, x12, 0
    sub  x15, x30, x13
    addi x15, x15, -1
    bn.add w31, w31, w31 # Clear flags.

    loop x15, 4
      bn.lid x10, 0(x14)
      bn.subb w22, w22, w27
      bn.sid x10, 0(x14++)
      bn.xor w27, w27, w27

    addi x13, x13, 1

  # The last iteration is special. No corrective subtraction is needed.
  bn.lid x10, 0(x12)
  bn.mov w24, w20
  bn.mov w25, w22
  jal x1, mul256_w24xw25
  bn.sid x11, 0(x12++)

  ret

/**
 * Unrolled 512=256x256 bit multiplication.
 *
 * Returns c = a * b.
 *
 * Flags: No flags are set in this subroutine.
 *
 * @param[in] w24: a, first operand
 * @param[in] w25: b, second operand
 * @param[out] [w26, w27]: c, result
 *
 * clobbered registers: w26, w27
 * clobbered flag groups: None
 */
mul256_w24xw25:
  bn.mulqacc.z          w24.0, w25.0,  0
  bn.mulqacc            w24.1, w25.0, 64
  bn.mulqacc.so  w26.L, w24.0, w25.1, 64
  bn.mulqacc            w24.2, w25.0,  0
  bn.mulqacc            w24.1, w25.1,  0
  bn.mulqacc            w24.0, w25.2,  0
  bn.mulqacc            w24.3, w25.0, 64
  bn.mulqacc            w24.2, w25.1, 64
  bn.mulqacc            w24.1, w25.2, 64
  bn.mulqacc.so  w26.U, w24.0, w25.3, 64
  bn.mulqacc            w24.3, w25.1,  0
  bn.mulqacc            w24.2, w25.2,  0
  bn.mulqacc            w24.1, w25.3,  0
  bn.mulqacc            w24.3, w25.2, 64
  bn.mulqacc.so  w27.L, w24.2, w25.3, 64
  bn.mulqacc.so  w27.U, w24.3, w25.3,  0
  ret
