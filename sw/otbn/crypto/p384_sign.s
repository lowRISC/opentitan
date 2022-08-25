/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for ECDSA signature generation and constant-time
 *   scalar multiplication.
 */

 .section .text

/**
 * Convert projective coordinates of a P-384 curve point to affine coordinates
 *
 * returns P = (x_a, y_a) = (x/z mod p, y/z mod p)
 *              where P is a valid P-384 curve point,
 *                    x_a and y_a are the resulting affine coordinates of the
 *                      curve point,
 *                    x,y and z are a set of projective coordinates of the
 *                      point and
 *                    p is the modulus of the P-384 underlying finite field.
 *
 * This routine computes the affine coordinates for a set of projective
 * coordinates of a valid P-384 curve point. The routine performs the required
 * divisions by computing the multiplicative modular inverse of the
 * projective z-coordinate in the underlying finite field of the P-384 curve.
 * For inverse computation Fermat's little theorem is used, i.e.
 * we compute z^-1 = z^(p-2) mod p.
 * For exponentiation a 16 step addition chain is used.
 * Source of the addition chain is the addchain project:
 * https://github.com/mmcloughlin/addchain/
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w26,w25]: x, x-coordinate of curve point (projective).
 * @param[in]  [w26,w25]: y, y-coordinate of curve point (projective).
 * @param[in]  [w30,w29]: z, z-coordinate of curve point (projective).
 * @param[in]  [w13, w12]: p, modulus of P-384.
 * @param[in]  w31: all-zero.
 * @param[out] [w26, w25]: x_a, affine x-coordinate of resulting point.
 * @param[out] [w28, w27]: y_a, affine y-coordinate of resulting point.
 *
 * clobbered registers: w0 to w28
 * clobbered flag groups: FG0
 */
proj_to_affine_p384:

  /* Exp: 0b10 = 2*0b1
     Val: r10 = z^2 mod p
          [w17,w16] <= [w30,w29]^2 mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  bn.mov    w16, w29
  bn.mov    w17, w30
  jal       x1, p384_mulmod_p

  /* Exp: 0b11 = 0b1+0b10
     Val: r11 <= z*r10 mod p
          [w17,w16] <= [w30,w29]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p

  /* Exp: 0b110 = 2*0b11
     Val: r110 = r11^2 mod p
          [w17,w16] <= [w17,w16]^2 mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, p384_mulmod_p

  /* Exp: 0b111 = 0b1+0b110
     Val: r111 <= z*r110  mod p
          [w1,w0] = [w17,w16] <= [w30,w29]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* Exp: 0b111000 = 0b111<<3
     Val: r111000 <= r111^(2^3)  mod p
          [w17,w16] <= [w17,w16]^(2^3) mod [w13,w12] */
  loopi     3, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop

  /* Exp: 0b1111111 = 0b111+0b111000
     Val: r1111111 <= r111*r111000 mod p
          [w3,w2] = [w17,w16] <= [w1,w0]*[w17,w16] mod [w13,w12] */
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, p384_mulmod_p
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* Exp: 2^12-1 = (0b1111111<<6)+0b111111
     Val: r_12_1 <= r111111^(2^6)*r111111 mod p
          [w5,w4] = [w17,w16] <= [w17,w16]^(2^6)*[w17,w16] mod [w13,w12] */
  loopi     6, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, p384_mulmod_p
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* Exp: 2^24-1 = ((2^12-1)<<12)+(2^12-1)
     Val: r_24_1 <= r_12_1^(2^12)*r12_1 mod p
          [w17,w16] <= [w17,w16]^(2^12)*[w5,w4] mod [w13,w12] */
  loopi     12, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w4
  bn.mov    w11, w5
  jal       x1, p384_mulmod_p

  /* Exp: 2^30-1 = ((2^24-1)<<6)+0b111111
     Val: r_30_1 <= r_24_1^(2^6)*r111111 mod p
          [w3, w2] = [w17,w16] <= [w17,w16]^(2^6)*[w3,w2] mod [w13,w12] */
  loopi     6, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, p384_mulmod_p
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* Exp: 2^31-1 <= (2^30-1)*2+0b1
     Val: r_31_1 <= r30_1^2*z mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^2*[w30,w29] mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, p384_mulmod_p
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* Exp: 2^32-1 <= (2^30-1)*2+0b1
     Val: r_32_1 <= r31_1^2*z mod p
          [w9,w8] = [w17,w16] <= [w17,w16]^2*[w30,w29] mod [w13,w12] */
  bn.mov    w10, w16
  bn.mov    w11, w17
  jal       x1, p384_mulmod_p
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p
  bn.mov    w9, w16
  bn.mov    w8, w17

  /* Exp: 2^63-1 <= ((2^32-1)<<31)+(2^31-1)
     Val: r_63_1 <= r_32_1^(2^31)*r_31_1 mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^(2^31)*[w7,w6] mod [w13,w12] */
  loopi     31, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, p384_mulmod_p
  bn.mov    w6, w16
  bn.mov    w7,w17

  /* Exp: 2^126-1 = ((2^63-1)<<63) + (2^63-1)
     Val: r_126_1 <= r_63_1^(2^63)*r_63_1 mod p
          [w7,w6] = [w17,w16] <= [w17,w16]^(2^63)*[w7,w6] mod [w13,w12] */
  loopi     63, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, p384_mulmod_p
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* Exp: 2^252-1 = ((2^126-1)<<126)+(2^126-1)
     Val: r_252_1 <= r_126_1^(2^63)*r_126_1 mod p
          [w17,w16] <= [w17,w16]^(2^126)*[w7,w6] mod [w13,w12] */
  loopi     126, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w6
  bn.mov    w11, w7
  jal       x1, p384_mulmod_p

  /* Exp: 2^255-1 = ((2^252-1)<<3)+0b111
     Val: r_255_1 <= r_252_1^(2^3)*r111 mod p
          [w17,w16] <= [w17,w16]^(2^3)*[w1,w0] mod [w13,w12] */
  loopi     3, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w0
  bn.mov    w11, w1
  jal       x1, p384_mulmod_p

  /* Exp: p-2 = ((((((2^255-1)<<33)+(2^32-1))<<94)+(2^30-1))<<2)+0b1
     Val: x_inv <=((r_255_1^(2^33)*r_32_1)^(2^94)*r_30_1)^(2^2)*z mod p
          [w17,w16] <= (([w17,w16]^(2^33)*[w9,w8])^(2^94)*[w3,w2])^(2^2)
                       *[w30,w29] mod [w13,w12] */
  loopi     33, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w9
  bn.mov    w11, w8
  jal       x1, p384_mulmod_p
  loopi     94, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, p384_mulmod_p
  loopi     2, 4
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_p
    nop
  bn.mov    w10, w29
  bn.mov    w11, w30
  jal       x1, p384_mulmod_p

  /* store inverse [w1,w0] <= [w17,w16] = z_inv*/
  bn.mov w0, w16
  bn.mov w1, w17

  /* convert x-coordinate to affine space
     [w26,w25] <= [w17,w16] = x_a <= x/z = x*z_inv = [w26,w25]*[w1,w0] mod p */
  bn.mov    w10, w25
  bn.mov    w11, w26
  jal       x1, p384_mulmod_p
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* convert y-coordinate to affine space
     [w28,w27] <= [w17,w16] = y_a <= y/z = y*z_inv = [w28,w27]*[w1,w0] mod p */
  bn.mov    w10, w27
  bn.mov    w11, w28
  bn.mov    w16, w0
  bn.mov    w17, w1
  jal       x1, p384_mulmod_p
  bn.mov    w27, w16
  bn.mov    w28, w17

  ret


/**
 * Fetch curve point from dmem, randomize z-coordinate and store point in dmem
 *
 * returns P = (x, y, z) = (x_a*z, y_a*z, z)
 *         with P being a valid P-384 curve point in projective coordinates
 *              x_a and y_a being the affine coordinates as fetched from dmem
 *              z being a randomized z-coordinate
 *
 * This routines fetches the affine x- and y-coordinates of a curve point from
 * dmem and computes a valid set of projective coordinates. The z-coordinate is
 * randomized and x and y are scaled appropriately. The resulting projective
 * coordinates are stored at dmem[dptr_p_p] using 6 consecutive 256-bit cells,
 * i.e. each coordinate is stored 512 bit aligned, little endian.
 * This routine runs in constant time.
 *
 * @param[in]  x20: dptr_x, pointer to dmem location containing affine
 *                          x-coordinate of input point
 * @param[in]  x21: dptr_y, pointer to dmem location containing affine
 *                          y-coordinate of input point
 * @param[in]  [w15, w14]: u[383:0] lower 384 bit of Barrett constant u for
 *                                    modulus p
 * @param[in]  [w13, w12]: p, modulus of P-384 underlying finite field
 * @param[in]  w31: all-zero
 * @param[in]  x18: dptr_p_p, pointer to dmem location to store resulting point
 *                            in projective space
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the upper limb of projective y-coordinate.
 *
 * clobbered registers: x10, x11 to x13
  *                     w2, w3, w8 to w11, w16 to w24, w29, w30
 * clobbered flag groups: FG0
 */
store_proj_randomize:

  /* get a 384-bit random number from URND
    [w3, w2] = random(384) */
  bn.wsrr   w2, 2
  bn.wsrr   w3, 2
  bn.rshi   w3, w31, w3 >> 128

  /* reduce random number
     [w2, w3] = z <= [w2, w3] mod p */
  bn.sub   w10, w2, w12
  bn.subb  w11, w3, w13
  bn.sel   w2, w2, w10, C
  bn.sel   w3, w3, w11, C

  bn.mov w10, w2
  bn.mov w11, w3

  /* store z-coordinate
     dmem[x20+128] = [w10, w11] */
  li        x10, 10
  li        x11, 11
  bn.sid    x10, 128(x18)
  bn.sid    x11, 160(x18)

  /* fetch x-coordinate from dmem
     [w16, w17] = x <= [dmem[dptr_x], dmem[dptr_x+32]] */
  li x12, 16
  li x13, 17
  bn.lid    x12,  0(x20)
  bn.lid    x13, 32(x20)

  /* scale and store x-coordinate
     [dmem[dptr_p_p], dmem[dptr_p_p+32]] = [w17, w16] =
       x_p <= [w11, w10] * [w17, w16] = z*x  mod p */

  jal       x1, p384_mulmod_p
  bn.sid    x12,  0(x18)
  bn.sid    x13, 32(x18)

  /* fetch y-coordinate from dmem
     [w11, w10] = x <= [dmem[dptr_y], dmem[dptr_y+32]] */
  bn.lid    x12,  0(x21)
  bn.lid    x13, 32(x21)

  /* scale and store y-coordinate
     [dmem[dptr_p_p+64], dmem[dptr_p_p+96]] = [w17, w16] =
       y_p <= [w11, w10] * [w17, w16] = z*y  mod p */
  bn.mov w10, w2
  bn.mov w11, w3
  jal       x1, p384_mulmod_p
  bn.sid    x12, 64(x18)
  bn.sid    x13, 96(x18)

  ret


/**
 * P-384 scalar point multiplication in affine space
 *
 * returns R = k*P = k*(x_p, y_p)
 *         where R, P are valid P-384 curve points in affine coordinates,
 *               k is a 384-bit scalar.
 *
 * This routine performs scalar multiplication based on the group laws
 * of Weierstrass curves.
 * A constant time double-and-add algorithm (sometimes referred to as
 * double-and-add-always) is used.
 * Due to the P-384 optimized implementations of the internally called routines
 * for point addition and doubling, this routine is limited to P-384 curves.
 * The routine makes use of blinding by additive splitting the
 * exponent/scalar d into two shares. The double-and-add loop operates on both
 * shares in parallel applying Shamir's trick.
 *
 * @param[in]  x9: dptr_rnd, pointer to location in dmem containing random
 *                           number to be used for additive splitting of scalar
 * @param[in]  x19: dptr_k, pointer to scalar k (0 < k < n) in dmem
 * @param[in]  x20: dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]  x21: dptr_y, pointer to affine y-coordinate in dmem
 * @param[in]  x28: dptr_b, pointer to domain parameter b of P-384 in dmem
 * @param[in]  x30: dptr_sp, pointer to 704 bytes of scratchpad memory in dmem
 * @param[in]  [w13, w12]: p, modulus of P-384 underlying finite field
 * @param[in]  [w11, w10]: n, domain parameter of P-384 curve
 *                            (order of base point G)
 * @param[in]  w31: all-zero
 * @param[out] [w26, w25]: x_a, affine x-coordinate of resulting point R.
 * @param[out] [w28, w26]: y_a, affine y-coordinate of resulting point R.
 *
 * Scratchpad memory layout:
 * The routine expects at least 704 bytes of scratchpad memory at dmem
 * location 'scratchpad' (sp). Internally the scratchpad is used as follows:
 * dptr_sp     .. dptr_sp+191: point P, projective
 * dptr_sp+192 .. dptr_sp+255: s0, 1st share of scalar
 * dptr_sp+256 .. dptr_sp+447: point 2P, projective
 * dptr_sp+448 .. dptr_sp+511: s1, 2nd share of scalar
 * dptr_sp+512 .. dptr_sp+703: point Q, projective
 *
 * Projective coordinates of a point are kept in dmem in little endian format
 * with the individual coordinates 512 bit aligned. The coordinates are stored
 * in x,y,z order (i.e. x at lowest, z at highest address). Thus, a 384 bit
 * curve point occupies 6 consecutive 256-bit dmem cells.
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x10, x11 to x13, x18, x26, x27, w0 to w30
 * clobbered flag groups: FG0
 */
scalar_mult_int_p384:

  /* set regfile pointers to in/out regs of Barrett routine. Set here to avoid
     resetting in very call to point addition routine */
  li        x22, 10
  li        x23, 11
  li        x24, 16
  li        x25, 17

  /* fetch externally supplied random number from dmem
     [w1, w0] = dmem[dptr_rnd] = [dmem[x9], dmem[x9+32]] = rnd */
  li        x2, 0
  bn.lid    x2++, 0(x9)
  bn.lid    x2++, 32(x9)

  /* 1st share (reduced rnd)
     s0 = [w1, w0] <= rnd mod n = [w1, w0] mod [w11, w10] */
  bn.sub    w9, w0, w10
  bn.subb   w8, w1, w11
  bn.sel    w0, w0, w9, C
  bn.sel    w1, w1, w8, C

  /* load scalar k from dmem
     [w3, w2] = k <= dmem[dptr_k] = [dmem[x19], dmem[x19+32]] */
  bn.lid    x2++, 0(x19)
  bn.lid    x2, 32(x19)

  /* 2nd share (k-s0)
     s1 = [w3, w2] <= k - s0 mod n = [w2, w3] - [w1, w0] mod [w11, w10] */
  bn.sub    w2, w2, w0
  bn.subb   w3, w3, w1
  bn.add    w8, w2, w10
  bn.addc   w9, w3, w11
  bn.sel    w2, w8, w2, C
  bn.sel    w3, w9, w3, C

  /* left align both shares for probing of MSB in loop body */
  bn.rshi   w1, w1, w0 >> 128
  bn.rshi   w0, w0, w31 >> 128
  bn.rshi   w3, w3, w2 >> 128
  bn.rshi   w2, w2, w31 >> 128

   /* store shares in scratchpad */
  li        x2, 0
  bn.sid    x2++, 192(x30)
  bn.sid    x2++, 224(x30)
  bn.sid    x2++, 448(x30)
  bn.sid    x2++, 480(x30)

  /* get randomized projective coodinates of curve point
     P = (x_p, y_p, z_p) = dmem[dptr_sp] = (x*z mod p, y*z mod p, z) */
  add       x18, x30, 0
  jal       x1, store_proj_randomize

  /* double point P
     2P = ([w30,w29], [w28,w27], [w26, w25]) <= 2*P */
  add       x27, x30, x0
  add       x26, x30, x0
  jal       x1, proj_add_p384

  /* store point 2P in scratchpad @w30+256
     dmem[dptr_sc+256] = [w30:w25] = 2P */
  li        x2, 25
  bn.sid    x2++, 256(x30)
  bn.sid    x2++, 288(x30)
  bn.sid    x2++, 320(x30)
  bn.sid    x2++, 352(x30)
  bn.sid    x2++, 384(x30)
  bn.sid    x2++, 416(x30)

  /* init point Q = (0,1,0) for double-and-add in scratchpad */
  /* dmem[x26] = dmem[dptr_sc+512] = Q = (0,1,0) */
  addi      x26, x30, 512
  li        x2, 30
  bn.addi   w30, w31, 1
  bn.sid    x2++, 64(x26)
  bn.sid    x2, 0(x26)
  bn.sid    x2, 32(x26)
  bn.sid    x2, 96(x26)
  bn.sid    x2, 128(x26)
  bn.sid    x2, 160(x26)

  /* double-and-add loop with decreasing index */
  loopi     384, 85

    /* double point Q
       Q = ([w30,w29], [w28,w27], [w26, w25]) <= Q + dmem[x27] */
    add       x27, x26, x0
    jal       x1, proj_add_p384

    /* store Q in dmem
     dmem[x26] = dmem[dptr_sc+512] <= [w30:w25] */
    li        x2, 25
    bn.sid    x2++, 0(x26)
    bn.sid    x2++, 32(x26)
    bn.sid    x2++, 64(x26)
    bn.sid    x2++, 96(x26)
    bn.sid    x2++, 128(x26)
    bn.sid    x2++, 160(x26)

    /* Probe if MSb of either of the two scalars (rnd or d-rnd) but not both
       is 1.
       If only one MSb is set, select P for addition.
       If both MSbs are set, select 2P for addition.
       (If neither MSB is set, 2P will be selected but result discarded.) */
    li        x2, 0
    bn.lid    x2++, 224(x30)
    bn.lid    x2, 480(x30)
    bn.xor    w8, w0, w1
    /* Create conditional offeset into scratchpad.
       if (s0[512] xor s1[512]) x27 <= x30 else x27 <= x30+256 */
    csrrs     x3, 0x7c0, x0
    xori      x3, x3, -1
    andi      x3, x3, 2
    slli      x27, x3, 7
    add       x27, x27, x30

    /* Reload randomized projective coodinates for curve point P.
       P = (x_p, y_p, z_p) = dmem[dptr_sp] <= (x*z mod p, y*z mod p, z) */
    jal       x1, store_proj_randomize

    /* Add points Q+P or Q+2P depending on offset in x27.
       Q_a = ([w30,w29], [w28,w27], [w26, w25]) <= Q + dmem[x27] */
    jal       x1, proj_add_p384

    /* load shares from scratchpad
       [w1, w0] = s0; [w3, w2] = s1 */
    li        x2, 0
    bn.lid    x2++, 192(x30)
    bn.lid    x2++, 224(x30)
    bn.lid    x2++, 448(x30)
    bn.lid    x2++, 480(x30)

    /* M = s0[511] | s1[511] */
    bn.or     w8, w1, w3

    /* load q from scratchpad
        Q = ([w9,w8], [w7,w6], [w5,w4]) <= dmem[x26] */
    li        x2, 4
    bn.lid    x2++, 0(x26)
    bn.lid    x2++, 32(x26)
    bn.lid    x2++, 64(x26)
    bn.lid    x2++, 96(x26)
    bn.lid    x2++, 128(x26)
    bn.lid    x2++, 160(x26)

    /* select either Q or Q_a
       if M: Q = ([w30,w29], [w28,w27], [w26, w25]) <= Q else: Q <= Q_a */
    bn.sel    w25, w25, w4, M
    bn.sel    w26, w26, w5, M
    bn.sel    w27, w27, w6, M
    bn.sel    w28, w28, w7, M
    bn.sel    w29, w29, w8, M
    bn.sel    w30, w30, w9, M

    /* store Q in dmem
     dmem[x26] = dmem[dptr_sc+512] <= [w30:w25] */
    li        x2, 25
    bn.sid    x2++, 0(x26)
    bn.sid    x2++, 32(x26)
    bn.sid    x2++, 64(x26)
    bn.sid    x2++, 96(x26)
    bn.sid    x2++, 128(x26)
    bn.sid    x2++, 160(x26)

    /* left shift both shares
       s0 <= s0 << 1 ; s1 <= s1 << 1 */
    bn.add    w0, w0, w0
    bn.addc   w1, w1, w1
    bn.add    w2, w2, w2
    bn.addc   w3, w3, w3
    /* store both shares in scratchpad */
    li        x2, 0
    bn.sid    x2++, 192(x30)
    bn.sid    x2++, 224(x30)
    bn.sid    x2++, 448(x30)
    bn.sid    x2++, 480(x30)


    /* Get a fresh random number from URND and scale the coordinates of 2P.
       (scaling each proj. coordinate by same factor results in same point) */

    /* get a 384-bit random number from URND */
    bn.wsrr   w2, 2
    bn.wsrr   w3, 2
    bn.rshi   w3, w31, w3 >> 128

    /* reduce random number
      [w2, w3] = z <= [w2, w3] mod p */
    bn.sub    w10, w2, w12
    bn.subb   w11, w3, w13
    bn.sel    w2, w2, w10, C
    bn.sel    w3, w3, w11, C

    /* scale all coordinates in scratchpad */
    li        x2, 16
    li        x3, 17
    /* x-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 256(x30)
    bn.lid    x3, 288(x30)
    jal       x1, p384_mulmod_p
    bn.sid    x2, 256(x30)
    bn.sid    x3, 288(x30)
    /* y-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 320(x30)
    bn.lid    x3, 352(x30)
    jal       x1, p384_mulmod_p
    bn.sid    x2, 320(x30)
    bn.sid    x3, 352(x30)
    /* z-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 384(x30)
    bn.lid    x3, 416(x30)
    jal       x1, p384_mulmod_p
    bn.sid    x2, 384(x30)
    bn.sid    x3, 416(x30)

  /* convert coordinates to affine space */
  jal       x1, proj_to_affine_p384

  ret


/**
 * Externally callable wrapper for P-384 scalar point multiplication
 *
 * returns R = k*P = k*(x_p, y_p)
 *         where R, P are valid P-384 curve points in affine coordinates,
 *               k is a 384-bit scalar..
 *
 * Sets up context and calls the internal scalar multiplication routine.
 * This routine runs in constant time.
 *
 * @param[in]  dmem[0]: dK, pointer to location in dmem containing scalar k
 * @param[in]  dmem[4]: dRnd, pointer to location in dmem containing random
 *                        number for blinding
 * @param[in]  dmem[20]: dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]  dmem[22]: dptr_y, pointer to affine y-coordinate in dmem
 *
 * 384-bit quantities have to be provided in dmem in little-endian format,
 * 512 bit aligned, with the highest 128 bit set to zero.
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30
 *                      w0 to w30
 * clobbered flag groups: FG0
 */
.globl scalar_mult_p384
scalar_mult_p384:

  /* set dmem pointer to point x-coordinate */
  la        x20, dptr_x
  lw        x20, 0(x20)

  /* set dmem pointer to point y-coordinate */
  la        x21, dptr_y
  lw        x21, 0(x21)

  /* set dmem pointer to scalar k */
  la        x19, dptr_k
  lw        x19, 0(x19)

  /* set pointer to blinding parameter */
  la        x9, dptr_rnd
  lw        x9, 0(x9)

  /* set dmem pointer to domain parameter b */
  la        x28, p384_b

  /* set dmem pointer to scratchpad */
  la        x30, scratchpad

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load domain parameter n (order of base point)
     [w11, w10] = n = dmem[p384_n] */
  li        x2, 10
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* init all-zero reg */
  bn.xor    w31, w31, w31

  jal       x1, scalar_mult_int_p384

  /* store result in dmem */
  li        x2, 25
  bn.sid    x2++, 0(x20)
  bn.sid    x2++, 32(x20)
  bn.sid    x2++, 0(x21)
  bn.sid    x2++, 32(x21)

  ret

/**
 * Externally callable routine for P-384 base point multiplication
 *
 * returns Q = d (*) G
 *         where Q is a resulting valid P-384 curve point in affine
 *                   coordinates,
 *               G is the base point of curve P-384, and
 *               d is a 384-bit scalar.
 *
 * Sets up context and calls the internal scalar multiplication routine.
 * This routine runs in constant time.
 *
 * @param[in]  dmem[0]: dptr_d, pointer to location in dmem containing
 *                      scalar d.
 * @param[in]  dmem[20]: dptr_x, pointer to result buffer for x-coordinate
 * @param[in]  dmem[24]: dptr_y, pointer to result buffer for y-coordinate
 * @param[in]  dmem[28]: dptr_rnd, pointer to location in dmem containing
 *                       random number for blinding.
 *
 * 384-bit quantities have to be provided in dmem in little-endian format,
 * 512 bit aligned, with the highest 128 bit set to zero.
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 correspond
 *        to the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30
 *                      w0 to w30
 * clobbered flag groups: FG0
 */
.globl p384_base_mult
p384_base_mult:

  /* set dmem pointer to x-coordinate of base point*/
  la        x20, p384_gx

  /* set dmem pointer to y-coordinate of base point */
  la        x21, p384_gy

  /* set dmem pointer to scalar d */
  la        x19, dptr_d
  lw        x19, 0(x19)

  /* set pointer to blinding parameter */
  la        x9, dptr_rnd
  lw        x9, 0(x9)

  /* set dmem pointer to domain parameter b */
  la        x28, p384_b

  /* set dmem pointer to scratchpad */
  la        x30, scratchpad

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load domain parameter n (order of base point)
     [w11, w10] = n = dmem[p384_n] */
  li        x2, 10
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* init all-zero reg */
  bn.xor    w31, w31, w31

  jal       x1, scalar_mult_int_p384

  /* set dmem pointer to point x-coordinate */
  la        x20, dptr_x
  lw        x20, 0(x20)

  /* set dmem pointer to point y-coordinate */
  la        x21, dptr_y
  lw        x21, 0(x21)

  /* store result in dmem */
  li        x2, 25
  bn.sid    x2++, 0(x20)
  bn.sid    x2++, 32(x20)
  bn.sid    x2++, 0(x21)
  bn.sid    x2++, 32(x21)

  ret


/**
 * Variable-time modular multiplicative inverse computation
 *
 * returns x_inv = x^-1 mod m
 *
 * This routine computes the modular multiplicative inverse for any x < m in
 * the finite field GF(m) where m is prime.
 *
 * For inverse computation, Fermat's little theorem is used, i.e.
 * we compute x^-1 = x^(m-2) mod m.
 * For exponentiation we use a standard, variable-time (!) square and multiply
 * algorithm.
 *
 * This routine is mainly intended to be used for inversion of scalars in
 * context of the P-384 curve. In theory, it can be used with any 384-bit
 * modulus m with a corresponding 385-bit Barrett constant u,
 * where u[383:192] = 0.
 *
 * Note: When used for P-384 scalar inversion, the routine will need 672 calls
 * to the multiplication routine. By using an adder chain this could be reduced
 * to ~433 multiplications, however, at the cost of a significant codes size
 * increase.
 *
 * Note: This routine runs in variable-time w.r.t. the modulus. It should only
 * be used with a non-secret modulus.
 *
 * @param[in]  [w13, w12]: m, 384 bit modulus
 * @param[in]  w14: k, Solinas constant (2^384 - m) (max. length 191 bits).
 * @param[in]  [w30, w29]: x, 384 bit operand
 * @param[in]  w31, all-zero
 * @param[out] [w17, w16]: x_inv, modular multiplicative inverse
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, w2, w3, w10, w11, w16 to w24
 * clobbered flag groups: FG0
 */
mod_inv_n_p384:

  /* subtract 2 from modulus for Fermat's little theorem
     [w13,w12] <= m - 2 = [w11,w10]-2 (left aligned) */
  bn.subi   w2, w12, 2
  bn.subb   w3, w13, w31
  bn.rshi   w3, w3, w2 >> 128
  bn.rshi   w2, w2, w31 >> 128

  /* init square and multiply: [w17,w16] = 1 */
  bn.addi   w16, w31, 1
  bn.mov    w17, w31

  /* square and multiply loop */
  loopi     384, 12

    /* square: [w17,w16] <= [w17, w16]*[w11,w10] mod [w13, w12] */
    bn.mov    w10, w16
    bn.mov    w11, w17
    jal       x1, p384_mulmod_n

    /* shift MSB into carry flag
       [w3,w2] = 2*[w3,w2] = [w3,w2] << 1 */
    bn.add    w2, w2, w2
    bn.addc   w3, w3, w3

    /* skip multiplication if C flag not set */
    csrrs     x2, 0x7c0, x0
    andi      x2, x2, 1
    beq       x2, x0, nomul

    /* multiply: [w17,w16] <= [w17, w16]*[w30,w29] mod [w13, w12] */
    bn.mov    w10, w29
    bn.mov    w11, w30
    jal       x1, p384_mulmod_n

    nomul:
    nop

  ret


/**
 * P-384 ECDSA signature generation
 *
 * returns the signature as the pair r, s with
 *         r = x_1  mod n
 *     and s = k^(-1)(msg + r*d)  mod n
 *         where x_1 is the affine x-coordinate of the curve point k*G,
 *               G is the curve's base point,
 *               k is a supplied secret random number,
 *               n is the order of the base point G of P-256,
 *               msg is the message to be signed, and
 *               d is the private key.
 *
 * This routine runs in constant time.
 *
 * @param[in]  dmem[0]: dptr_k, pointer to a 384 bit random secret in dmem
 * @param[in]  dmem[4]: dptr_rnd, pointer to location in dmem containing
 *                       a 384-bit random number for blinding
 * @param[in]  dmem[8]: dptr_msg, pointer to the message to be signed in dmem
 * @param[in]  dmem[12]: dptr_r, pointer to dmem location where s component
 *                               of signature will be placed
 * @param[in]  dmem[16]: dptr_s, pointer to dmem location where r component
 *                               of signature will be placed
 * @param[in]  dmem[28]: dptr_d, pointer to private key d in dmem
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x28, x30
 *                      w0 to w31
 * clobbered flag groups: FG0
 */
.globl p384_sign
p384_sign:
  /* init all-zero reg */
  bn.xor    w31, w31, w31

  /* set dmem pointer to domain parameter b */
  la        x28, p384_b

  /* set dmem pointer to base point x-coordinate */
  la        x20, p384_gx

  /* set dmem pointer to base point y-coordinate */
  la        x21, p384_gy

  /* set dmem pointer to secret random scalar k */
  la        x19, dptr_k
  lw        x19, 0(x19)

  /* set pointer to blinding parameter */
  la        x9, dptr_rnd
  lw        x9, 0(x9)

  /* set dmem pointer to scratchpad */
  la        x30, scratchpad

  /* load domain parameter p (modulus)
     [w13, w12] <= p = dmem[dptr_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load domain parameter n (order of base point)
     [w11, w10] = n = dmem[p384_n] */
  li        x2, 10
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* scalar multiplication with base point
     [w28:w25] <= (x_1, y_1) = k*G */
  jal       x1, scalar_mult_int_p384

  /* store r of signature in dmem: dmem[dptr_r] <= r = [w26,w25] */
  li        x2, 25
  la        x3, dptr_r
  lw        x3, 0(x3)
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)

  /* load secret random number k from dmem
     [w30,w29] <= k = dmem[dptr_k] */
  li        x2, 29
  bn.lid    x2++, 0(x19)
  bn.lid    x2++, 32(x19)

  /* load domain parameter n (order of base point)
     [w13, w12] <= p = dmem[p384_n] */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Compute Solinas constant k for modulus n (we know it is only 191 bits, so
     no need to compute the high part):
     w14 <= 2^256 - n[255:0] = (2^384 - n) mod (2^256) = 2^384 - n */
  bn.sub    w14, w31, w12

  /* modular multiplicative inverse of k
     [w3, w2] <= [w17, w16] <= k^(-1) mod n */
  jal       x1, mod_inv_n_p384
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* load private key d from dmem
     [w11,w10] <= d = dmem[dptr_d] */
  li        x2, 10
  la        x3, dptr_d
  lw        x3, 0(x3)
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* [w17, w16] <= k^(-1)*d mod n = [w17, w16] * [w11, w10] mod [w13, w12] */
  jal       x1, p384_mulmod_n

  /*  [w5, w4] <= [w17, w16]
        <= r * (k^(-1)*d) mod n = [w26, w25] * [w17, w16] mod [w13, w12] */
  bn.mov    w10, w25
  bn.mov    w11, w26
  jal       x1, p384_mulmod_n
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* load message from dmem
     [w11, w10] <= msg = dmem[dptr_msg] */
  li        x2, 10
  la        x3, dptr_msg
  lw        x3, 0(x3)
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* [w17, w16] <= k^(-1) * msg = [w3, w2]*[w17, w16] mod n */
  bn.mov    w16, w2
  bn.mov    w17, w3
  jal       x1, p384_mulmod_n

  /* [w28, w27] <= s' = k^(-1)*msg + k^(-1)*r*d  = [w17, w16] + [w5, w4]*/
  bn.add    w27, w16, w4
  bn.addc   w28, w17, w5

  /* reduce s: [w28, w27] <= s <= s' mod n = [w28, w27] mod [w13, w12] */
  bn.sub    w10, w27, w12
  bn.subb   w11, w28, w13
  bn.sel    w27, w27, w10, C
  bn.sel    w28, w28, w11, C

  /* store s of signature in dmem: dmem[dptr_s] <= s = [w28, w27] */
  li        x2, 27
  la        x3, dptr_s
  lw        x3, 0(x3)
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)

  ret


/* pointers and scratchpad memory */
.section .data

/* pointer to k (dptr_k) */
.globl dptr_k
dptr_k:
  .zero 4

/* pointer to rnd (dptr_rnd) */
.globl dptr_rnd
dptr_rnd:
  .zero 4

/* pointer to msg (dptr_msg) */
.globl dptr_msg
dptr_msg:
  .zero 4

/* pointer to R (dptr_r) */
.globl dptr_r
dptr_r:
  .zero 4

/* pointer to S (dptr_s) */
.globl dptr_s
dptr_s:
  .zero 4

/* pointer to X (dptr_x) */
.globl dptr_x
dptr_x:
  .zero 4

/* pointer to Y (dptr_y) */
.globl dptr_y
dptr_y:
  .zero 4

/* pointer to D (dptr_d) */
.globl dptr_d
dptr_d:
  .zero 4

/* 704 bytes of scratchpad memory */
scratchpad:
  .zero 704
