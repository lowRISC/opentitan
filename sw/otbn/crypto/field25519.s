/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * This library contains arithmetic for the finite field modulo the prime
 * p = 2^255-19, which is used for both the X25519 key exchange and the Ed25519
 * signature scheme.
 */

/**
 * Multiply two field elements and reduce modulo p.
 *
 * Returns c = (a * b) mod p.
 *
 * The inputs a and b must be at most 2^255 bits, although it is not necessary
 * for them to be fully reduced modulo p. This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w22: a, first operand, a < 2^255
 * @param[in]  w23: b, second operand, b < 2^255
 * @param[in]  w30: constant, 38
 * @param[in]  w31: all-zero
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[out] w22: c, result
 *
 * clobbered registers: w18, w20 to w22
 * clobbered flag groups: FG0
 */
.globl fe_mul
fe_mul:
  /* Partial products for multiply-reduce:

     | a0b0    | a0b1    | a0b2    | a0b3 |
     |         | a1b0    | a1b1    | a1b2 |
     |         |         | a2b0    | a2b1 |
     |         |         |         | a3b0 |
     |         |         |         |      |
     | a1b3*38 | a2b3*38 | a3b3*38 |      |
     | a2b2*38 | a3b2*38 |         |      |
     | a3b1*38 |         |         |      |

   We can further optimize by computing the highest-weight partial products
   as t = (a0b2 + a1b1 + a2b0 + a3b3*38 + (a0b3 + a1b2 + a2b1 + a3b0) << 64)
   ahead of time and multiplying the upper half by 38 as well:

     | a0b0       | a0b1    | t0 | t1 |
     |            | a1b0    |    |    |
     |            |         |    |    |
     |            |         |    |    |
     |            |         |    |    |
     | a1b3*38    | a2b3*38 |    |    |
     | a2b2*38    | a3b2*38 |    |    |
     | a3b1*38    | t3*38   |    |    |
     | t2*38      |         |    |    |

  */

  /* Precompute b3*38 at an offset of 128 and store in w18 (this step also
     clears the lower part of w18, which is important later).
       w18.U <= b3*38 */
  bn.mulqacc.wo.z w18, w23.3, w30.0, 128

  /* Accumulate partial products from the top two limbs first, and store the
     result in ACC and w18.U such that:
       ACC <= t2 + t3 << 64
       w18 <= t0 << 128 + t1 << 192 */
  bn.mulqacc.z          w22.0, w23.2, 0 /* a0b2 */
  bn.mulqacc            w22.1, w23.1, 0 /* a1b1 */
  bn.mulqacc            w22.2, w23.0, 0 /* a2b0 */
  bn.mulqacc            w22.3, w18.2, 0 /* a3*((b3*38)[63:0]) */
  bn.mulqacc            w22.0, w23.3, 64 /* a0b3 */
  bn.mulqacc            w22.1, w23.2, 64 /* a1b2 */
  bn.mulqacc            w22.2, w23.1, 64 /* a2b1 */
  bn.mulqacc            w22.3, w23.0, 64 /* a3b0 */
  bn.mulqacc.so  w18.U, w22.3, w18.3, 64 /* a3*((b3*38) >> 64) */

  /* Reduce the high part modulo p. This guarantees a full reduction because
     the written-back value is at most (2^128 - 1) * 2^128 < 2 * p.
       w18 <= (t0 << 128 + t1 << 192) mod p */
  bn.addm    w18, w18, w31

  /* Accumulate partial products that need to be multiplied by 38 and are
     fully within the first 256 bits of the result. Result max. 194 bits.
       w20 <= (a1b3 + a2b2 + a3b1 + t2) + (a2b3 + a3b2 + t3) << 64 */
  bn.mulqacc            w22.1, w23.3, 0  /* a1b3 */
  bn.mulqacc            w22.2, w23.2, 0  /* a2b2 */
  bn.mulqacc            w22.3, w23.1, 0  /* a3b1 */
  bn.mulqacc            w22.2, w23.3, 64 /* a2b3 */
  bn.mulqacc.wo    w20, w22.3, w23.2, 64 /* a3b2 */

  /* Multiply the accumulator by 38, storing the result in the accumulator.
     This value is at most 200 bits and so will not overflow the accumulator.
       ACC <= w20*38 */
  bn.mulqacc.z          w20.0, w30.0, 0
  bn.mulqacc            w20.1, w30.0, 64
  bn.mulqacc            w20.2, w30.0, 128
  bn.mulqacc            w20.3, w30.0, 192

  /* Continue accumulating partial products for the lower half of the
     product.
       w20 <= (a0b0 + a1b3*38 + a2b2*38 + a3b1*38 + t2*38)
              + (a0b1 + a1b0 + a2b3*38 + a3b2*38 + t3*38) << 64  */
  bn.mulqacc            w22.0, w23.0, 0   /* a0b0 */
  bn.mulqacc            w22.0, w23.1, 64  /* a0b1 */
  bn.mulqacc.wo    w20, w22.1, w23.0, 64  /* a1b0 */

  /* Add the high and low parts of the product.
      w22 <= (a * b) mod p */
  bn.addm    w22, w20, w18

  ret

/**
 * Square a field element and reduce modulo p.
 *
 * Returns c = (a * a) mod p.
 *
 * The input a must be at most 2^255 bits, although it is not necessary for it
 * to be fully reduced modulo p. This specialized squaring procedure is
 * slightly faster than `fe_mul`, because duplicated partial products can be
 * multiplied by two instead of being computed separately.
 *
 * Note: to cut down on code size at the expense of performance, we could use
 * `fe_mul` for all multiplications, but it's unlikely to be worth the tradeoff
 * given this is a small and frequently called routine.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w19: constant, 19
 * @param[in]  w22: a, operand, a < 2^255
 * @param[in]  w30: constant, 38
 * @param[in]  w31: all-zero
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[out] w22: c, result
 *
 * clobbered registers: w17, w18, w20 to w22
 * clobbered flag groups: FG0
 */
.globl fe_square
fe_square:
  /* Partial products for square:

     | a0a0    | a0a1*2  | a0a2*2  | a0a3*2 |
     |         |         | a1a1    | a1a2*2 |
     |         |         |         |        |
     | a1a3*76 | a2a3*76 | a3a3*38 |        |
     | a2a2*38 |         |         |        |

   Totally separate the ones with *2, so that (a^2 = x + 2y).

   x:
     | a0a0    |         |         |      |
     |         |         | a1a1    |      |

   y:
     |         | a0a1    | a0a2    | a0a3 |
     |         |         |         | a1a2 |
     |         |         |         |      |
     | a1a3*38 | a2a3*38 | a3a3*19 |      |
     | a2a2*19 |         |         |      |

   We can optimize the computation of y, as in fe_mul, by computing the highest
   limbs first:
     t = a0a2 + a3a3*19 + (a0a3 + a1a2) << 64

   y:
     |         | a0a1    | t0 | t1 |
     |         |         |    |    |
     | a1a3*38 | a2a3*38 |    |    |
     | a2a2*19 |         |    |    |
     | t2*38   | t3*38   |    |    |

  */

  /* w17 <= a2*19 */
  bn.mulqacc.wo.z    w17, w22.2, w19.0, 0

  /* w18[255:128] <= a3*19
     w18[127:0] <= 0 */
  bn.mulqacc.wo.z    w18, w22.3, w19.0, 128

  /* Compute t, the sum of partial products for highest two limbs of y.
       w18[255:128] = t0 + t1 << 64
       ACC = t1 + t2 << 64 */
  bn.mulqacc.z            w22.0, w22.2, 0
  bn.mulqacc              w22.3, w18.2, 0
  bn.mulqacc              w22.3, w18.3, 64
  bn.mulqacc              w22.0, w22.3, 64
  bn.mulqacc.so    w18.U, w22.1, w22.2, 64

  /* Reduce this high part of y. Since it is at most 2^256 - 2^128 < 2p, one
     modular addition of zero is enough. */
  bn.addm   w18, w18, w31

  /* Add remaining elements of y that need to be multiplied by 38. The result
     is max. 191 bits (a3 is 63 bits and t3 is at most 1 bit).
       w20 <= t2 + t3 << 64 + a1*a3 + (a2*a3) << 64 */
  bn.mulqacc              w22.1, w22.3, 0
  bn.mulqacc.wo      w20, w22.2, w22.3, 64

  /* Multiply the accumulator by 38.
       ACC <= t2*38 + (t3*38) << 64 + a1*a3*38 + (a2*a3*38) << 64 */
  bn.mulqacc.z            w20.0, w30.0, 0
  bn.mulqacc              w20.1, w30.0, 64
  bn.mulqacc              w20.2, w30.0, 128

  /* Add the remaining elements of y.
       w20 <= t2*38 + (t3*38) << 64 + a1*a3*38 + (a2*a3*38) << 64
              + (a2*a2*19) + a0*a1 << 64 */
  bn.mulqacc              w22.2, w17.0, 0
  bn.mulqacc              w22.2, w17.1, 64
  bn.mulqacc.wo      w20, w22.0, w22.1, 64

  /* Add the high and low parts of y.
       w20 <= y */
  bn.addm   w20, w20, w18

  /* Compute x.
       w21 <= a0*a0 + (a1*a1) << 128 */
  bn.mulqacc.z            w22.0, w22.0, 0
  bn.mulqacc.wo      w21, w22.1, w22.1, 128

  /* Reduce x modulo p. Its maximum value is (2^64-1)^2 + ((2^64-1)^2 << 128),
     which is < 2p, so one modular addition of zero is enough. */
  bn.addm   w21, w21, w31

  /* Return (x + 2y) mod p.
       w22 <= (w20 + w20 + w21) mod p = (x + 2*y) mod p = (a * a) mod p */
  bn.addm   w20, w20, w20
  bn.addm   w22, w20, w21
  ret

/**
 * Compute the inverse of an element in the finite field modulo (2^255-19).
 *
 * Returns c = (a^(-1)) mod p.
 *
 * Uses Fermat's Little Theorem, which states that for any nonzero element a of
 * the finite field modulo a prime p, then a^(p-1) mod p = 1. A corrolary of
 * this theorem is that (a * (a^(p-2))) mod p = 1, so a^(p-2) is a
 * multiplicative inverse of a modulo p.
 *
 * To compute a^(p-2), we use a square-and-multiply algorithm. This chain of
 * squares and multiplies is modified from curve25519-donna
 * (https://github.com/agl/curve25519-donna/blob/f7837adf95a2c2dcc36233cb02a1fb34081c0c4a/curve25519-donna-c64.c#L403),
 * which is in turn a modified version of the (qhasm) reference implementation
 * published with the original paper.
 *
 * The main difference between this implementation and donna is that we attempt
 * to minimize bn.mov instructions by making sure multiplies/squares always use
 * the same temporary variables/registers.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w19: constant, 19
 * @param[in]  w16: a, first operand, a < p
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[in]  w30: constant, 38
 * @param[in]  w31: all-zero
 * @param[out] w22: c, result
 *
 * clobbered registers: w14, w15, w17, w18, w20 to w23
 * clobbered flag groups: FG0
 */
.globl fe_inv
fe_inv:
  /* w22 <= w16^2 = a^2 */
  bn.mov  w22, w16
  jal     x1, fe_square
  /* w23 <= w22 = a^2 */
  bn.mov  w23, w22

  /* w22 <= w22^4 = a^8 */
  jal     x1, fe_square
  jal     x1, fe_square

  /* w22 <= w22 * w23 = a^10 */
  jal     x1, fe_mul
  /* w15 <= w22 = a^10 */
  bn.mov  w15, w22

  /* w22 <= w22 * w16 = a^11 */
  bn.mov  w23, w16
  jal     x1, fe_mul
  /* w14 <= w22 <= a^11 */
  bn.mov  w14, w22

  /* w22 <= w15^2 = a^20 */
  bn.mov  w22, w15
  jal     x1, fe_square

  /* w22 <= w22 * w14 = a^31 = a^(2^5 - 1) */
  bn.mov  w23, w14
  jal     x1, fe_mul
  /* w23 <= w22 = a^(2^5 - 1) */
  bn.mov  w23, w22

  /* w22 <= w22^(2^5) = a^(2^10-2^5) */
  loopi   5,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^10-1) */
  jal     x1, fe_mul
  /* w23 <= w22 <= a^(2^10-1) */
  bn.mov  w23, w22
  /* w15 <= w22 <= a^(2^10-1) */
  bn.mov  w15, w22

  /* w22 <= w22^(2^10) = a^(2^20-2^10) */
  loopi   10,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^20-1) */
  jal     x1, fe_mul
  /* w23 <= w22 <= a^(2^20-1) */
  bn.mov  w23, w22

  /* w22 <= w22^(2^20) = a^(2^40-2^20) */
  loopi   20,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^40-1) */
  jal     x1, fe_mul

  /* w22 <= w22^(2^10) = a^(2^50-2^10) */
  loopi   10,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w15 = a^(2^50-1) */
  bn.mov  w23, w15
  jal     x1, fe_mul
  /* w23 <= w22 <= a^(2^50-1) */
  bn.mov  w23, w22
  /* w15 <= w22 <= a^(2^50-1) */
  bn.mov  w15, w22

  /* w22 <= w22^(2^50) = a^(2^100-2^50) */
  loopi   50,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^100-1) */
  jal     x1, fe_mul
  /* w23 <= w22 <= a^(2^100-1) */
  bn.mov  w23, w22

  /* w22 <= w22^(2^100) = a^(2^200-2^100) */
  loopi   100,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w23 = a^(2^200-1) */
  jal     x1, fe_mul

  /* w22 <= w22^(2^50) = a^(2^250-2^50) */
  loopi   50,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w15 = a^(2^250-1) */
  bn.mov  w23, w15
  jal     x1, fe_mul

  /* w22 <= w22^(2^5) = a^(2^255-2^5) */
  loopi   5,2
    jal     x1, fe_square
    nop

  /* w22 <= w22 * w14 = a^(2^255 - 2^5 + 11) = a^(2^255 - 21) = a^(p-2) */
  bn.mov  w23, w14
  jal     x1, fe_mul

  ret
