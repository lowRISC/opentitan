/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * This library contains code for X25519, for use in elliptic-curve Diffie
 * Hellman key exchange.
 *
 * Helpful references:
 * RFC: https://datatracker.ietf.org/doc/html/rfc7748
 * Academic paper: https://www.iacr.org/cryptodb/archive/2006/PKC/3351/3351.pdf
 */

/**
 * Top-level X25519 function, as defined in RFC 7748.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w8: enc(k), encoded scalar (256-bit random number)
 * @param[in]  w9: enc(u), encoded Montgomery u-coordinate (256 bits)
 * @param[out] w22: result, X25519(k, u) as an encoded u-coordinate
 *
 * clobbered registers: w2 to w24
 * clobbered flag groups: FG0
 */
.globl X25519
X25519:
  /* Prepare all-zero register. */
  bn.xor   w31, w31, w31
  /* Prepare constant for field operations.
     w19 <= 19  */
  bn.addi  w19, w31, 19

  /* Load modulus from DMEM.
       MOD <= dmem[modulus25519] = 2^255 - 19 = p */
  li      x2, 2
  la      x3, modulus25519
  bn.lid  x2, 0(x3)
  bn.wsrw MOD, w2

  /* Decode scalar. From RFC 7748, section 5:

   "For X25519, in order to decode 32 random bytes as an integer scalar, set
    the three least significant bits of the first byte and the most significant bit
    of the last to zero, set the second most significant bit of the last byte to 1
    and, finally, decode as little-endian." */

  /* w8 <= (w8 >> 3) = enc(k) >> 3 */
  bn.rshi  w8, w31, w8 >> 3
  /* w8 <= w8 << 5 = ((enc(k) >> 3) << 5) mod 2^256 */
  bn.rshi  w8, w8, w31 >> 251
  /* w8 <= 2^254 + (w8 >> 2) = ((enc(k) >> 3) << 3) mod 2^254 + 2^254 = k*/
  bn.addi  w7, w31, 1
  bn.rshi  w8, w7, w8 >> 2

  /* Decode point u-coordinate. As specified in RFC 7748, section 5, we must
     zero the most significant bit and accept non-canonical values (i.e. cases
     where p <= u) as if they had been reduced modulo p. */

  /* w7 <= ~w31 = 2^256 - 1 */
  bn.not   w7, w31
  /* w7 <= w7 >> 1 = 2^255 - 1 */
  bn.rshi  w7, w31, w7 >> 1
  /* w9 <= w9 & w7 = enc(u) mod 2^255 */
  bn.and   w9, w9, w7
  /* w9 <= w9 mod p <= (enc(u) mod 2^255) mod p = u */
  bn.addm  w9, w9, w31

  /* Note that, in contrast to Ed25519, the given point does not have to be
     validated; see the original Curve25519 paper for discussion (search
     for "small-subgroup attacks" and "free key validation").
     https://www.iacr.org/cryptodb/archive/2006/PKC/3351/3351.pdf */

  /* Perform scalar multiplication.
       w22 <= scalar_mult(k, u) = X25519(k, u) */
  jal     x1, scalar_mult

  /* Since the scalar multiplication routine has already reduced its result
     modulo p and OTBN is little-endian, encoding the result is a no-op. */

  ret

/**
 * Elliptic-curve scalar multiplication for Curve25519.
 *
 * Returns B = kA.
 *
 * Multiplies a point on the curve (A) with a scalar (k). Uses the Montgomery
 * ladder algorithm as in RFC 7748. For the Montgomery ladder, we only need to
 * consider the u-coordinate of curve points.
 *
 * See RFC 7748, section 5:
 *   https://datatracker.ietf.org/doc/html/rfc7748#section-5
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w8: k, 255-bit scalar value
 * @param[in]  w9: u, Montgomery u-coordinate of point A (k < p)
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  w31, all-zero
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[out] w22: result, Montgomery u-coordinate of point kA
 *
 * clobbered registers: w2 to w7, w10 to w18, w20 to w24
 * clobbered flag groups: FG0
 */
scalar_mult:

  /* Load the constant a24:
       w24 <= dmem[a24] = 121665 */
  li      x2, 24
  la      x3, a24
  bn.lid  x2, 0(x3)

  /* Set initial values. From RFC 7748:

     x_2 = 1
     z_2 = 0
     x_3 = u
     z_3 = 1
     swap = 0
 */

  /* x_2 = w10 <= 1 */
  bn.addi  w10, w31, 1
  /* z_2 = w12 <= 0 */
  bn.mov   w12, w31
  /* x_3 = w11 <= u */
  bn.mov   w11, w9
  /* z_3 = w13 <= 1 */
  bn.addi  w13, w31, 1
  /* swap = w15 <= 0 */
  bn.mov   w15, w31

  /* Initialize w4 for loop.
       w14 <= (k << 1) mod 2^256 */
  bn.rshi  w14, w8, w31 >> 255

  /* Main loop. From RFC 7748 (with `ladderstep` factored into a separate step):

     For t = bits-1 down to 0:
         k_t = (k >> t) & 1
         swap ^= k_t
         (x_2, x_3) = cswap(swap, x_2, x_3)
         (z_2, z_3) = cswap(swap, z_2, z_3)
         swap = k_t

         ladderstep(u, x_2, x_3, z_2, z_3)

     Loop invariants:
       w14 = (k << (255-t)) mod 2^256
       w9 = u

     Loop temporary registers: w6, w7
  */
  loopi   255, 12
    /* w7 <= w14 >> 255 = (k << (255-t)) mod 2^256 >> 255 = k[t] = k_t */
    bn.rshi  w7, w31, w14 >> 255
    /*  w14 <= w14 << 1 = (k << (255-(t-1)) mod 2^256 */
    bn.rshi  w14, w14, w31 >> 255
    /* swap = w15 = w15 ^ w7 = swap ^ k_t */
    bn.xor   w15, w15, w7

    /* Note: The xor above set FG0.Z if and only if swap ^ k_t is zero. */

    /* Conditionally swap x_2 and x_3. */

    /* w6 <= if swap =? 0 then x_2 else x_3 */
    bn.sel  w6, w10, w11, FG0.Z
    /* x_3 = w11 <= if swap =? 0 then x_3 else x_2 */
    bn.sel  w11, w11, w10, FG0.Z
    /* x_2 = w10 <= w6 = if swap =? 0 then x_2 else x_3 */
    bn.mov  w10, w6

    /* Conditionally swap z_2 and z_3. */

    /* w6 <= if swap =? 0 then z_2 else z_3 */
    bn.sel  w6, w12, w13, FG0.Z
    /* z_3 = w13 <= if swap =? 0 then z_3 else z_2 */
    bn.sel  w13, w13, w12, FG0.Z
    /* z_2 = w12 <= w6 = if swap =? 0 then z_2 else z_3 */
    bn.mov  w12, w6

    /* swap = w15 <= w7 = k_t */
    bn.mov  w15, w7

    jal     x1, ladderstep
    nop

  /* Loop done; final steps. From RFC 7748:

     (x_2, x_3) = cswap(swap, x_2, x_3)
     (z_2, z_3) = cswap(swap, z_2, z_3)
     Return x_2 * (z_2^(p - 2))
  */

  /* Set the FG0.Z flag if swap (w15) is 0. */
  bn.add  w15, w15, w31

  /* Conditionally swap x_2 and x_3. */

  /* w6 <= if swap =? 0 then x_2 else x_3 */
  bn.sel  w6, w10, w11, FG0.Z
  /* x_3 = w11 <= if swap =? 0 then x_3 else x_2 */
  bn.sel  w11, w11, w10, FG0.Z
  /* x_2 = w10 <= w6 = if swap =? 0 then x_2 else x_3 */
  bn.mov  w10, w6

  /* Conditionally swap z_2 and z_3. */

  /* w6 <= if swap =? 0 then z_2 else z_3 */
  bn.sel  w6, w12, w13, FG0.Z
  /* z_3 = w13 <= if swap =? 0 then z_3 else z_2 */
  bn.sel  w13, w13, w12, FG0.Z
  /* z_2 = w12 <= w6 = if swap =? 0 then z_2 else z_3 */
  bn.mov  w12, w6

  /* w22 <= fe_inv(w12) = z_2^(p-2) */
  bn.mov  w16, w12
  jal     x1, fe_inv
  /* w22 <= w22 * w10 = (z_2^(p-2)) * x_2 */
  bn.mov  w23, w10
  jal     x1, fe_mul

  ret

/**
 * Performs the core arithmetic step of the Montgomery ladder.
 *
 * This subroutine is intended to be used as part of a Montgomery ladder
 * implementation. It performs the core arithmetic in the main loop, i.e. the
 * following steps (from RFC 7748, section 5):
 *   A = x_2 + z_2
 *   AA = A^2
 *   B = x_2 - z_2
 *   BB = B^2
 *   E = AA - BB
 *   C = x_3 + z_3
 *   D = x_3 - z_3
 *   DA = D * A
 *   CB = C * B
 *   x_3 = (DA + CB)^2
 *   z_3 = x_1 * (DA - CB)^2
 *   x_2 = AA * BB
 *   z_2 = E * (AA + a24 * E)
 *
 * All arithmetic (+, -, *, ^) above is in the finite field GF(2^255-19).
 *
 * TODO: investigate alternative laddersteps, such as the one in
 * curve25519-donna, which may be faster.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] w9: x_1, Montgomery u-coordinate of point A (k < p)
 * @param[in] w19: constant, w19 = 19
 * @param[in] w24: constant a24 = 121665
 * @param[in] w31: all-zero
 * @param[in] MOD: p, modulus = 2^255 - 19
 * @param[in,out] w10:  x_2
 * @param[in,out] w11:  x_3
 * @param[in,out] w12:  z_2
 * @param[in,out] w13:  z_3
 *
 * clobbered registers: w2 to w5, w10 to w13, w17, w18, w20 to w23
 * clobbered flag groups: FG0
 */
ladderstep:
  /* First, compute the new x_2 and z_2:
       A = x_2 + z_2
       AA = A^2
       B = x_2 - z_2
       BB = B^2
       E = AA - BB
       x_2 = AA * BB
       z_2 = E * (AA + a24 * E) */

  /* w2 <= w10 + w12 = x_2 + z_2 = A */
  bn.addm  w2, w10, w12
  /* w3 <= w2^2 = A^2 = AA */
  bn.mov   w22, w2
  jal      x1, fe_square
  bn.mov   w3, w22
  /* w4 <= w10 - w12 = x_2 - z_2 = B */
  bn.subm  w4, w10, w12
  /* w22 <= w4^2 = B^2 = BB */
  bn.mov   w22, w4
  jal      x1, fe_square
  /* w5 <= w3 - w22 = AA - BB = E */
  bn.subm  w5, w3, w22
  /* x_2 = w10 <= w22 * w3 = BB * AA */
  bn.mov   w23, w3
  jal      x1, fe_mul
  bn.mov   w10, w22
  /* w23 <= w5 = E */
  bn.mov   w23, w5
  /* TODO: create faster, specialized fe_mul for a24 */
  /* w22 <= w24 * w23 = a24 * E */
  bn.mov   w22, w24
  jal      x1, fe_mul
  /* w22 <= w3 + w22 = AA + (a24 * E) */
  bn.add   w22, w3, w22
  /* z_2 = w12 <= w22 * w23 = (AA + a24 * E) * E */
  jal      x1, fe_mul
  bn.mov   w12, w22

  /* Now, compute the new x_3 and z_3, using A and B from the computation
     above:
       C = x_3 + z_3
       D = x_3 - z_3
       DA = D * A
       CB = C * B
       x_3 = (DA + CB)^2
       z_3 = x_1 * (DA - CB)^2 */

  /* w22 <= w11 + w13 = x_3 + z_3 = C */
  bn.addm  w22, w11, w13
  /* w4 <= w22 * w4 = C * B = CB */
  bn.mov   w23, w4
  jal      x1, fe_mul
  bn.mov   w4, w22
  /* w22 <= w11 - w13 = x_3 - z_3 = D */
  bn.subm  w22, w11, w13
  /* w2 <= w22 * w2 = D * A = DA */
  bn.mov   w23, w2
  jal      x1, fe_mul
  bn.mov   w2, w22
  /* w22 <= w2 + w4 <= DA + CB */
  bn.addm  w22, w2, w4
  /* x_3 = w11 <= w22^2 = (DA + CB)^2 */
  jal      x1, fe_square
  bn.mov   w11, w22
  /* w22 <= w2 - w4 <= DA - CB */
  bn.subm  w22, w2, w4
  /* w22 <= w22^2 = (DA - CB)^2 */
  jal      x1, fe_square
  /* z_3 = w13 <= w22 * w9 = (DA - CB)^2 * x_1 */
  bn.mov   w23, w9
  jal      x1, fe_mul
  bn.mov   w13, w22

  ret

.data

/* Modulus p = 2^255 - 19. */
.balign 32
modulus25519:
  .word 0xffffffed
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0x7fffffff

/* Constant (a - 2) / 4 for Curve25519 = 121665 (see RFC 7748, section 5). */
.balign 32
a24:
.word 0x0001db41
.zero 28
