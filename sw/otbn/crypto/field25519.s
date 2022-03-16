/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * This library contains arithmetic for the finite field modulo the prime
 * p = 2^255-19, which is used for both the X25519 key exchange and the Ed25519
 * signature scheme.
 */


/**
 * Fully reduce a 510-bit number modulo p.
 *
 * Returns c = a mod p.
 *
 * Uses Solinas/pseudo-Mersenne reduction, which is based on the observation
 * that if a large number x is split into two so that the lower 255 bits are x0
 * and all bits above 255 are x1, then:
 *
 *   x = x0 + (2^255 * x1) \equiv (x0 + (19 * x1)) (mod p)
 *
 * If x is large, then x0 + 19 * x1 will be much smaller than x, because 19 <<
 * 2^255. This step can be repeated as necessary until a conditional
 * subtraction is enough to fully reduce.
 *
 * Note about register notations: in this code, [a:b] indicates that the
 * registers are adjacent and their contents can be logically concatenated to
 * get a single larger value. Otherwise, the notation is [a,b].
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  [w21:w20]: a, number to be reduced (a < 2^510)
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[in]  w31: all-zero
 * @param[out] w22: c, result = a mod p
 *
 * clobbered registers: w18, w20 to w22
 * clobbered flag groups: FG0
 */
fe_reduce:
  /* First Solinas step (reducing modulo 2p = 2^256-38). */

  /* Multiply the high bits by 38 (fits in 64bx256b multiply). Note that the
     last multiplication result is zero; it exists only to write back the
     accumulator from previous multiplies.
     w18,w22 <= 19 * (2 * w21) = 38 * a[509:256] */
  bn.add                w18, w21, w21
  bn.mulqacc.z          w19.0, w18.0, 0
  bn.mulqacc.so  w22.L, w19.0, w18.1, 64
  bn.mulqacc            w19.0, w18.2, 0
  bn.mulqacc.so  w22.U, w19.0, w18.3, 64
  bn.mulqacc.wo  w18,   w19.0, w31.0, 0

  /* Add to low bits.
     [w21:w20] <= w20 + [w18,w22] = a[255:0] + (38 * a[509:256]) = r1 */
  bn.add  w20, w20, w22
  bn.addc w21, w31, w18

  /* First Solinas step is complete. At this point, the new intermediate result
     r1 is at most 261 bits, because:
                        a[509:256] = 254 bits
                   38 * a[509:256] = 260 bits
        a[255:0] + 38 * a[509:256] = 261 bits */

  /* Begin second Solinas step (reducing by p = 2^255 - 19 this time). */

  /* Extract the high 6 bits.
     w21 <= [w21:w20] >> 255 = r1[260:255] */
  bn.rshi w21, w21, w20 >> 255

  /* Extract the low 255 bits.
     w20 <= r1[254:0] */
  bn.rshi w20, w20, w31 >> 255
  bn.rshi w20, w31, w20 >> 1

  /* Multiply the high bits by 19 (fits in 64bx64b multiply).
     w21 <= w19 * w21 = 19 * r1[260:255] */
  bn.mulqacc.wo.z w21, w19.0, w21.0, 0

  /* Add to low bits (guaranteed by bounds not to carry).
     w20 <= r1[254:0] + (19 * r1[260:255]) = r2 */
  bn.add  w20, w20, w21

  /* Second Solinas step is complete. At this point, we know r2 < 2 * p,
     because of bounds implied by bit lengths:
       r1[254:0] + 19 * r1[260:255] <= 2^255 - 1 + 19 * (2^6 - 1) < 2 * p */

  /* Conditionally subtract modulus if p <= r2.
     w22 <= r2 mod p = a mod p */
  bn.addm  w22, w20, w31

  ret

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
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  w22: a, first operand, a < 2^255
 * @param[in]  w23: b, second operand, b < 2^255
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[in]  w31: all-zero
 * @param[out] w22: c, result
 *
 * clobbered registers: w18, w20 to w22
 * clobbered flag groups: FG0
 */
.globl fe_mul
fe_mul:
  /* Compute the raw 510-bit product.
     [w21:w20] <= a * b */
  bn.mulqacc.z          w22.0, w23.0,  0
  bn.mulqacc            w22.1, w23.0, 64
  bn.mulqacc.so  w20.L, w22.0, w23.1, 64
  bn.mulqacc            w22.2, w23.0,  0
  bn.mulqacc            w22.1, w23.1,  0
  bn.mulqacc            w22.0, w23.2,  0
  bn.mulqacc            w22.3, w23.0, 64
  bn.mulqacc            w22.2, w23.1, 64
  bn.mulqacc            w22.1, w23.2, 64
  bn.mulqacc.so  w20.U, w22.0, w23.3, 64
  bn.mulqacc            w22.3, w23.1,  0
  bn.mulqacc            w22.2, w23.2,  0
  bn.mulqacc            w22.1, w23.3,  0
  bn.mulqacc            w22.3, w23.2, 64
  bn.mulqacc.so  w21.L, w22.2, w23.3, 64
  bn.mulqacc.so  w21.U, w22.3, w23.3,  0

  /* Reduce modulo p.
     w22 <= [w21:w20] mod p = (a * b) mod p */
  jal    x1, fe_reduce

  ret

/**
 * Square a field element and reduce modulo p.
 *
 * Returns c = (a * a) mod p.
 *
 * The input a must be at most 2^255 bits, although it is not necessary for it
 * to be fully reduced modulo p. This specialized squaring procedure is
 * slightly faster than fe_mul, because duplicated partial products can be
 * multiplied by two instead of being computed separately.  By optimizing for
 * this special case, we can use 10 multiplications and 4 additions instead of
 * 16 multiplications to compute the raw product.
 *
 * Note that this is only 2 instructions faster than fe_mul; if we need to cut
 * down on code size, we could try not using a specialized square. However,
 * this routine is called many, many times (especially in the inverse
 * computation) so those two instructions might add up to quite a bit in the
 * end.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  w22: a, operand, a < 2^255
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[in]  w31: all-zero
 * @param[out] w22: c, result
 *
 * clobbered registers: w17, w18, w20 to w22
 * clobbered flag groups: FG0
 */
.globl fe_square
fe_square:
  /* Compute the partial products that do NOT need to be multiplied by 2.
     [w21:w20] <= a0^2 + (a1^2 << 128) + (a2^2 << 256) + (a3^2 << 384) */
  bn.mulqacc.so.z  w20.L, w22.0, w22.0,  0
  bn.mulqacc.so    w20.U, w22.1, w22.1,  0
  bn.mulqacc.so    w21.L, w22.2, w22.2,  0
  bn.mulqacc.so    w21.U, w22.3, w22.3,  0

  /* Compute the partial products that do need to be multiplied by 2.
     [w18:w17] <= (a0a1 << 64) + (a0a2 << 128) + (a0a3 << 192)
                               + (a1a2 << 192) + (a1a3 << 256)
                               + (a2a3 << 320)                    */
  bn.mulqacc.so.z  w17.L, w22.0, w22.1, 64
  bn.mulqacc              w22.0, w22.2,  0
  bn.mulqacc              w22.0, w22.3, 64
  bn.mulqacc.so    w17.U, w22.1, w22.2, 64
  bn.mulqacc              w22.1, w22.3,  0
  bn.mulqacc.wo    w18,   w22.2, w22.3, 64

  /* Add the partial products.
     [w21:w20] <= [w21:w20] + [w18:w17] * 2 = a * a */
  bn.add  w20, w20, w17
  bn.addc w21, w21, w18
  bn.add  w20, w20, w17
  bn.addc w21, w21, w18

  /* Reduce modulo p.
     w22 <= [w21:w20] mod p = (a * a) mod p */
  jal    x1, fe_reduce

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
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  w16: a, first operand, a < p
 * @param[in]  MOD: p, modulus = 2^255 - 19
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
