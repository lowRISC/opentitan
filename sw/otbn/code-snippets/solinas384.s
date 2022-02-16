/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Constant time modular multiplication for P-384 based on Solinas reduction
 * algorithm.
 */

.section .text

/**
 * Unrolled 768=384x384 bit multiplication.
 *
 * Returns c = a x b.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w9, w8]: a, first operand, max. length 384 bit.
 * @param[in] [w11, w10]: b, second operand, max. length 384 bit.
 * @param[in] w31: all-zero.
 * @param[out] [w16, w15, w14]: c, result, max. length 768 bit.
 *
 * Clobbered flag groups: FG0
 */
mul384:
  bn.mulqacc.z          w8.0, w10.0,   0
  bn.mulqacc            w8.0, w10.1,  64
  bn.mulqacc.so w14.L,  w8.1, w10.0,  64
  bn.mulqacc            w8.0, w10.2,   0
  bn.mulqacc            w8.1, w10.1,   0
  bn.mulqacc            w8.2, w10.0,   0
  bn.mulqacc            w8.0, w10.3,  64
  bn.mulqacc            w8.1, w10.2,  64
  bn.mulqacc            w8.2, w10.1,  64
  bn.mulqacc.so w14.U,  w8.3, w10.0,  64
  bn.mulqacc            w8.0, w11.0,   0
  bn.mulqacc            w8.1, w10.3,   0
  bn.mulqacc            w8.2, w10.2,   0
  bn.mulqacc            w8.3, w10.1,   0
  bn.mulqacc            w9.0, w10.0,   0
  bn.mulqacc            w8.0, w11.1,  64
  bn.mulqacc            w8.1, w11.0,  64
  bn.mulqacc            w8.2, w10.3,  64
  bn.mulqacc            w8.3, w10.2,  64
  bn.mulqacc            w9.0, w10.1,  64
  bn.mulqacc.so w15.L,  w9.1, w10.0,  64
  bn.mulqacc            w8.1, w11.1,   0
  bn.mulqacc            w8.2, w11.0,   0
  bn.mulqacc            w8.3, w10.3,   0
  bn.mulqacc            w9.0, w10.2,   0
  bn.mulqacc            w9.1, w10.1,   0
  bn.mulqacc            w8.2, w11.1,  64
  bn.mulqacc            w8.3, w11.0,  64
  bn.mulqacc            w9.0, w10.3,  64
  bn.mulqacc.so w15.U,  w9.1, w10.2,  64
  bn.mulqacc            w8.3, w11.1,   0
  bn.mulqacc            w9.0, w11.0,   0
  bn.mulqacc            w9.1, w10.3,   0
  bn.mulqacc            w9.0, w11.1,  64
  bn.mulqacc.so w16.L,  w9.1, w11.0,  64
  bn.mulqacc.so w16.U,  w9.1, w11.1,   0

  ret

/**
 * Multiplication by the Solinas constant for P-384.
 *
 * Returns xK = x * (2^128 + 2^96 - 2^32 + 1)
 *
 * For P-384, Solinas reduction involves multiplying by the constant K (K =
 * 2^384 - modulus). We can efficiently compute the product x * K by expanding
 * to:
 *   xK = (x << 128) + (x << 96) - (x << 32) + x
 *
 * This routine runs in constant time.
 *
 * Flags: Flags correspond to the subtraction of (x << 32) from the high limb.
 *
 * @param[in] w4 x, input operand
 * @param[in] w31 all-zero
 * @param[out] [w7:w6] result
 *
 * Clobbered registers: w6, w7
 * Clobbered flag groups: FG0
 */
mul_k:
  /* [w7:w6] <= x + (x << 128) */
  bn.add  w6, w4, w4 << 128
  bn.addc w7, w31, w4 >> 128

  /* [w7:w6] <= x + (x << 128) + (x << 96) */
  bn.add  w6, w6, w4 << 96
  bn.addc w7, w7, w4 >> 160

  /* [w7:w6] <= x + (x << 128) + (x << 96) - (x << 32) = xK */
  bn.sub  w6, w6, w4 << 32
  bn.subb w7, w7, w4 >> 224

  ret


/**
 * 384-bit modular multiplication based on Solinas reduction algorithm.
 *
 * Returns c = a x b % m.
 *
 * Expects the two 384-bit operands a and b to be in "unsaturated" form: rather
 * than having 256 bits in the first limb and 128 bits in the second, we expect
 * 192 bits in each limb, so that a = w8 + w9 << 192 and b = w10 + w11 << 192.
 * The result c is returned in the same format (c = w29 + w30 << 192).
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] [w9, w8]: a, first operand, max. length 384 bit, a < m.
 * @param[in] [w11, w10]: b, second operand, max. length 384 bit, b < m.
 * @param[in] [w13, w12]: m, modulus, max. length 384 bit, 2^384 > m > 2^383.
 * @param[in] [p384_k]: k, precomputed reduction constant
 * @param[in] w31: all-zero.
 * @param[out] [w30, w29]: c, result, max. length 384 bit.
 *
 * Clobbered registers: w4 to w7, w14 to w16, w29, w30, acc
 * Clobbered flag groups: FG0
 */
solinas384:
  /* Compute the raw 768-bit product:
       ab = [w16:w14] <= a * b */
  jal     x1, mul384

  /* Construct a 256-bit mask that will be useful later on:
       w30 <= 2^256 - 1 */
  bn.not  w30, w31

  /* Solinas reduction step. Based on the observation that:
     (x + 2^384 * y) mod (2^384 - K) = (x + K * y) mod (2^384 - K). */

  /* Extract the high 128 bits from the middle term and the low 128 bits from
     the high term, then multiply by K:
       [w7:w6] <= ab[639:384] * K */
  bn.rshi w4, w16, w15 >> 128
  jal     x1, mul_k

  /* Isolate the lower 384 bits:
       w15 <= ab[383:256] */
  bn.and  w15, w15, w30 >> 128

  /* Add product to the lower 384 bits:
       [w15:w14] = ab[384:0] + (ab[639:384] * K) */
  bn.add  w14, w14, w6
  bn.addc w15, w15, w7

  /* Multiply the highest 128 bits of the product by K:
       [w7:w6] <= ab[767:640] * K */
  bn.rshi w4, w31, w16 >> 128
  jal     x1, mul_k

  /* Add product to the result to complete the reduction step:
       [w16:w14] = ab[384:0] + (ab[767:384] * K) */
  bn.add  w15, w15, w6
  bn.addc w16, w31, w7

  /* At this point, the intermediate result (henceforth "r") has at most 513
     bits (i.e. w16 is at most 1). Start another Solinas reduction step to
     reduce the bound further. */

  /* Multiply the high 129 bits by K:
       [w7:w6] <= r[512:384] * K */
  bn.rshi w4, w16, w15 >> 128
  jal     x1, mul_k

  /* Isolate the lower 384 bits:
       w15 <= r[383:256] */
  bn.and  w15, w15, w30 >> 128

  /* Add product to the lower 384 bits to complete the reduction step:
       [w15:w14] = r[384:0] + (r[513:384] * K) */
  bn.add  w14, w14, w6
  bn.addc w15, w15, w7

  /* At this point, the result is at most 385 bits, and a conditional
     subtraction is sufficient to fully reduce. */
  bn.sub  w29, w14, w12
  bn.subb w30, w15, w13

  /* If the subtraction underflowed (C is set), select the pre-subtraction
     result; otherwise, select the result of the subtraction. */
  bn.sel w29, w14, w29, C
  bn.sel w30, w15, w30, C

  /* return result: c =[w29, w30] =  a * b % m. */
  ret

/**
 * Externally callable wrapper for modular multiplication with
 * Solinas reduction.
 *
 * Returns c = a x b % m.
 *
 * @param[in]  dmem[first]: a, first operand, max. length 384 bit
 * @param[in]  dmem[second]: b, second operand, max. length 384 bit
 * @param[in]  dmem[modulus]: m, modulus, max. length 384 bit
 *                            with 2^384 > m > 2^383
 * @param[out] dmem[first]: c, result, max. length 384 bit.
 */
.section .text.start
.globl wrap_solinas384
wrap_solinas384:
  /* Initialize all-zero register. */
  bn.xor w31, w31, w31

  /* load first operand from dmem to [w9, w8] */
  li     x4, 8
  la     x5, first
  bn.lid x4++, 0(x5)
  bn.lid x4++, 32(x5)
  /* load second operand from dmem to [w11, w10] */
  la     x5, second
  bn.lid x4++, 0(x5)
  bn.lid x4++, 32(x5)
  /* load modulus from dmem to [w13, w12] */
  la     x5, modulus
  bn.lid x4++, 0(x5)
  bn.lid x4++, 32(x5)

  jal    x1, solinas384

  la     x5, out
  li     x4, 29
  bn.sid x4++, 0(x5)
  bn.sid x4++, 32(x5)

  ecall

.section .data

/* First operand. */
.balign 32
first:
.word 0x8f122951
.word 0x73ff314c
.word 0x7a097999
.word 0x2051536e
.word 0xb64b9530
.word 0xdce2294e
.word 0x005c06ab
.word 0x95b1756b
.word 0x69821679
.word 0x628540cf
.word 0x1eb1d98b
.word 0x24509793
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* Second operand. */
.balign 32
second:
.word 0x4d815c86
.word 0x7c37aa39
.word 0x0e92397c
.word 0xf6da2fc9
.word 0x617835eb
.word 0x52bcdb9c
.word 0xbb7f6aaa
.word 0xca809d63
.word 0x4c28c407
.word 0x476e9732
.word 0xd0face3d
.word 0x922eb7ed
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* Modulus.*/
.balign 32
modulus:
.word 0xffffffff
.word 0x00000000
.word 0x00000000
.word 0xffffffff
.word 0xfffffffe
.word 0xffffffff
.word 0x00000000
.word 0x00000000
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0x00000000
.word 0x00000000

/* Output buffer. */
.balign 32
out:
.zero 64

/*
Expected result in buffers [w30:w29]:

w29 | 0x5054372a_ba0d9ce3_b0d94772_06992345_c7b24eb1_f1fae9f6_2b1edb3d_83a27cdb
w30 | 0x00000000_00000000_00000000_00000000_a4fcf2c0_9d974be4_1adb3a1d_d50e68c1
*/
