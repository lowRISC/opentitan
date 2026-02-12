/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for internal scalar multiplication of curve points.
 */

 .section .text

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
 .globl store_proj_randomize
store_proj_randomize:

  /* get a 384-bit random number from URND
    [w17, w16] = random(384) */
  bn.wsrr   w16, 2
  bn.wsrr   w17, 2
  bn.rshi   w17, w31, w17 >> 128

  /* reduce random number
     [w23, w22] = z <= [w17, w16] mod p */
  bn.sub   w18, w16, w12
  bn.subb  w19, w17, w13
  bn.sel   w22, w16, w18, C
  bn.sel   w23, w17, w19, C

  /* Move z-coordinate into regs for later use
     [w3, w2] <= z, [w11, w10] <= z */
  bn.mov w2,  w22
  bn.mov w3,  w23
  bn.mov w10, w22
  bn.mov w11, w23

  /* store z-coordinate
     dmem[x20+128] = [w10, w11] */
  li        x10, 10
  li        x11, 11
  bn.sid    x10, 128(x18)
  bn.sid    x11, 160(x18)

  /* fetch x-coordinate from dmem
     [w16, w17] = x <= [dmem[dptr_x], dmem[dptr_x+32]] */
  li        x12, 16
  li        x13, 17
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
 * Wrapper function for P-384 scalar point multiplication in projective space.
 *
 * This function does not reblind the secret scalar before performing
 * the scalar multiplication.
 *
 * @param[in]  x17: dptr_k0, pointer to first share k0 of scalar k
 *                           (0 < k < n) in dmem (448-bit)
 * @param[in]  x19: dptr_k1, pointer to second share k1 of scalar k
 *                           (0 < k < n) in dmem (448-bit)
 * @param[in]  x20: dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]  x21: dptr_y, pointer to affine y-coordinate in dmem
 * @param[in]  x28: dptr_b, pointer to domain parameter b of P-384 in dmem
 * @param[in]  x30: dptr_sp, pointer to 704 bytes of scratchpad memory in dmem
 * @param[in]  [w13, w12]: p, modulus of P-384 underlying finite field
 * @param[in]  [w11, w10]: n, domain parameter of P-384 curve
 *                            (order of base point G)
 * @param[in]  w31: all-zero
 * @param[out]  [w26,w25]: x, x-coordinate of resulting point R (projective).
 * @param[out]  [w28,w27]: y, y-coordinate of resulting point R (projective).
 * @param[out]  [w30,w29]: z, z-coordinate of resulting point R (projective).
 *
 * clobbered registers: x2, x10, x11 to x13, x16, x18, x26, x27, w0 to w30
 * clobbered flag groups: FG0
 */
 .globl scalar_mult_int_p384
scalar_mult_int_p384:

  /* fetch 1st share of scalar from dmem
     s0 = [w2, w1] <= dmem[dptr_k0] = k0 */
  li        x2, 1
  bn.lid    x2++, 0(x17)
  bn.lid    x2,   32(x17)

  /* fetch 2nd share of scalar from dmem
     s1 = [w5, w4] <= dmem[dptr_k1] = k1 */
  li        x2, 4
  bn.lid    x2++, 0(x19)
  bn.lid    x2,   32(x19)

  /* Left align both shares for probing of MSB in loop body. */
  /* Zeroize w0 and w5 since they are not needed without reblinding. */

  /* Get some randomness to pad the shares. */
  bn.wsrr   w6, URND
  bn.rshi   w2, w2, w1 >> 192
  bn.rshi   w1, w1, w6 >> 192
  /* Set w0 to rand.
     It is unused in the unblinded scalar mult and will shift into other share regs. */
  bn.wsrr   w0, URND

  /* Get some randomness to pad the shares. */
  bn.wsrr   w6, URND
  bn.rshi   w5, w5, w4 >> 192
  bn.rshi   w4, w4, w6 >> 192
  /* Set w3 to rand.
     It is unused in the unblinded scalar mult and will shift into other share regs. */
  bn.wsrr   w3, URND

  /* Set the loop iteration variable for the multiplication. */
  addi      x16, x0, 448

  /* perform the scalar multiplication. */
  jal       x1, scalar_mult_int_p384_internal

  addi      x2, x0, 448
  beq       x2, x16, scalar_mult_int_p384_ret

  /* The number of iterations has been faulted; fail. */
  unimp
  unimp
  unimp

scalar_mult_int_p384_ret:
  ret

/**
 * Wrapper function for P-384 scalar point multiplication in projective space.
 *
 * This function reblinds the secret scalar before performing
 * the scalar multiplication.
 *
 * @param[in]  x17: dptr_k0, pointer to first share k0 of scalar k
 *                           (0 < k < n) in dmem (578-bit)
 * @param[in]  x19: dptr_k1, pointer to second share k1 of scalar k
 *                           (0 < k < n) in dmem (578-bit)
 * @param[in]  x20: dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]  x21: dptr_y, pointer to affine y-coordinate in dmem
 * @param[in]  x28: dptr_b, pointer to domain parameter b of P-384 in dmem
 * @param[in]  x30: dptr_sp, pointer to 704 bytes of scratchpad memory in dmem
 * @param[in]  [w13, w12]: p, modulus of P-384 underlying finite field
 * @param[in]  [w11, w10]: n, domain parameter of P-384 curve
 *                            (order of base point G)
 * @param[in]  w31: all-zero
 * @param[out]  [w26,w25]: x, x-coordinate of resulting point R (projective).
 * @param[out]  [w28,w27]: y, y-coordinate of resulting point R (projective).
 * @param[out]  [w30,w29]: z, z-coordinate of resulting point R (projective).
 *
 * clobbered registers: x2, x10, x11 to x13, x16, x18, x26, x27, w0 to w30
 * clobbered flag groups: FG0
 */
 .globl scalar_mult_int_p384_reblind
scalar_mult_int_p384_reblind:

  /* fetch 1st share of scalar from dmem
     s0 = [w2, w1, w0] <= dmem[dptr_k0] = k0 */
  li        x2, 0
  bn.lid    x2++, 0(x17)
  bn.lid    x2++, 32(x17)
  bn.lid    x2++, 64(x17)

  /* Dummy instruction to avoid consecutive share access. */
  bn.xor    w31, w31, w31

  /* fetch 2nd share of scalar from dmem
     s1 = [w5, w4, w3] <= dmem[dptr_k1] = k1 */
  bn.lid    x2++, 0(x19)
  bn.lid    x2++, 32(x19)
  bn.lid    x2,   64(x19)

  /* reblind the masked scalar. */
  jal       x1, p384_masked_scalar_reblind

  /* left align both shares for probing of MSB in loop body */

  /* Get some randomness to pad the shares. */
  bn.wsrr   w6, URND
  bn.rshi   w2, w2, w1 >> 66
  bn.rshi   w1, w1, w0 >> 66
  bn.rshi   w0, w0, w6 >> 66

  /* Get some randomness to pad the shares. */
  bn.wsrr   w6, URND
  bn.rshi   w5, w5, w4 >> 66
  bn.rshi   w4, w4, w3 >> 66
  bn.rshi   w3, w3, w6 >> 66

  /* Set the loop iteration variable for the multiplication. */
  addi      x16, x0, 578

  /* perform the scalar multiplication. */
  jal       x1, scalar_mult_int_p384_internal

  addi      x2, x0, 578
  beq       x2, x16, scalar_mult_int_p384_reblind_ret

  /* The number of iterations has been faulted; fail. */
  unimp
  unimp
  unimp

scalar_mult_int_p384_reblind_ret:
  ret

/**
 * P-384 scalar point multiplication in projective space
 *
 * returns R = k*P = k*(x_p, y_p)
 *         where P is a valid P-384 curve point in affine coordinates,
 *               k is a 384-bit scalar,
 *               R is a valid P-384 curve point in projective coordinates.
 *
 * This routine performs scalar multiplication based on the group laws
 * of Weierstrass curves.
 * A constant time double-and-add algorithm (sometimes referred to as
 * double-and-add-always) is used.
 * Due to the P-384 optimized implementations of the internally called routines
 * for point addition and doubling, this routine is limited to P-384 curves.
 * The routine makes use of blinding by additive splitting the
 * exponent/scalar d into two shares. The double-and-add loop operates on both
 * shares in parallel applying the Strauss-Shamir trick:
 * The routine receives the scalar in two shares k0, k1 such that
 *   k = (k0 + k1) mod n
 * The loop operates on both shares in parallel, computing (k0 + k1) * P as
 * follows:
 *  Q = (0, 1, 0) # origin
 *  for i in iter..0:
 *    Q = 2 * Q
 *    A = if (k0[i] ^ k1[i]) then P else 2P
 *    B = Q + A
 *    Q = if (k0[i] | k1[i]) then B else Q
 *
 * Each share k0/k1 is 578 bits (in the reblinded case) or 448 (in the non reblinded case),
 * even though it represents a 384-bit value.
 * This is a side-channel protection measure.
 *
 * 448 bit shares mean that we have 64 bits of blinding for each share.
 * 578 bit shares mean that we have 194 bits of blinding for each share.
 * 578 bits is the minimal number of bits needed to protect against window
 * attacks mentioned in Schindler.
 * https://csrc.nist.gov/csrc/media/events/workshop-on-elliptic-curve-cryptography-standards/documents/papers/session6-schindler-werner.pdf
 *
 * The reblinding is needed whenever vertical attack scenarios apply,
 * e.g. in case of ECDH and key generation.
 *
 * @param[in]  x16:          iter, number of loop iterations for the main loop
 * @param[in]  x20:          dptr_x, pointer to affine x-coordinate in dmem
 * @param[in]  x21:          dptr_y, pointer to affine y-coordinate in dmem
 * @param[in]  x28:          dptr_b, pointer to domain parameter b of P-384 in dmem
 * @param[in]  x30:          dptr_sp, pointer to 704 bytes of scratchpad memory in dmem
 * @param[in]  [w2, w1, w0]: k0, first share k0 of scalar k
 *                           (0 < k < n) (578-bit)
 * @param[in]  [w5, w4, w3]: k0, second share k0 of scalar k
 *                           (0 < k < n) (578-bit)
 * @param[in]  [w13, w12]:   p, modulus of P-384 underlying finite field
 * @param[in]  [w11, w10]:   n, domain parameter of P-384 curve
 *                              (order of base point G)
 * @param[in]  w31: all-zero
 * @param[out]  [w26,w25]: x, x-coordinate of resulting point R (projective).
 * @param[out]  [w28,w27]: y, y-coordinate of resulting point R (projective).
 * @param[out]  [w30,w29]: z, z-coordinate of resulting point R (projective).
 *
 * Scratchpad memory layout:
 * The routine expects at least 704 bytes of scratchpad memory at dmem
 * location 'scratchpad' (sp). Internally the scratchpad is used as follows:
 * dptr_sp     .. dptr_sp+191: point P, projective
 * dptr_sp+192 .. dptr_sp+287: s0, 1st share of scalar
 * dptr_sp+288 .. dptr_sp+479: point 2P, projective
 * dptr_sp+480 .. dptr_sp+575: s1, 2nd share of scalar
 * dptr_sp+576 .. dptr_sp+767: point Q, projective
 *
 * Projective coordinates of a point are kept in dmem in little endian format
 * with the individual coordinates 512 bit aligned. The coordinates are stored
 * in x,y,z order (i.e. x at lowest, z at highest address). Thus, a 384 bit
 * curve point occupies 6 consecutive 256-bit dmem cells.
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x7, x8, x10 to x13, x18, x26, x27, w0 to w30
 * clobbered flag groups: FG0
 */
scalar_mult_int_p384_internal:

  /* set regfile pointers to in/out regs of Barrett routine. Set here to avoid
     resetting in very call to point addition routine */
  li        x22, 10
  li        x23, 11
  li        x24, 16
  li        x25, 17
  la        x7, p_temp1
  la        x8, p_temp2

   /* store shares in scratchpad */
  li        x2, 0
  bn.sid    x2++, 192(x30)
  bn.sid    x2++, 224(x30)
  bn.sid    x2++, 256(x30)

  /* Dummy instruction to avoid consecutive share access. */
  bn.xor    w31, w31, w31

  bn.sid    x2++, 480(x30)
  bn.sid    x2++, 512(x30)
  bn.sid    x2,   544(x30)

  /* get randomized projective coodinates of curve point
     P = (x_p, y_p, z_p) = dmem[dptr_sp] = (x*z mod p, y*z mod p, z) */
  add       x18, x30, 0
  jal       x1, store_proj_randomize

  /* double point P
     2P = ([w30,w29], [w28,w27], [w26, w25]) <= 2*P */
  add       x27, x30, x0
  add       x26, x30, x0
  jal       x1, proj_add_p384

  /* store point 2P in scratchpad @x30+288
     dmem[dptr_sc+288] = [w30:w25] = 2P */
  li        x2, 25
  bn.sid    x2++, 288(x30)
  bn.sid    x2++, 320(x30)
  bn.sid    x2++, 352(x30)
  bn.sid    x2++, 384(x30)
  bn.sid    x2++, 416(x30)
  bn.sid    x2,   448(x30)

  /* init point Q = (0,1,0) for double-and-add in scratchpad */
  /* dmem[x26] = dmem[dptr_sc+512] = Q = (0,1,0) */
  addi      x26, x30, 576
  li        x2, 30
  bn.addi   w30, w31, 1
  bn.sid    x2++, 64(x26)
  bn.sid    x2, 0(x26)
  bn.sid    x2, 32(x26)
  bn.sid    x2, 96(x26)
  bn.sid    x2, 128(x26)
  bn.sid    x2, 160(x26)

  /* double-and-add loop with decreasing index */
  loop      x16, 157

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
    bn.sid    x2,   160(x26)

    /* Probe if MSb of either of the two scalars (rnd or d-rnd) but not both
       is 1.
       If only one MSb is set, select P for addition.
       If both MSbs are set, select 2P for addition.
       (If neither MSB is set, 2P will be selected but result discarded.)
       This is done based on both shares of d separately as follows:
       (d0 ^ d1) ? P : 2P = d0 ? (d1 ? 2P : P) : (d1 ? P : 2P). */

    /* Load the MSB of d0.
       M <= MSB(d0) */
    li        x2, 0
    bn.lid    x2, 256(x30)
    bn.or     w8, w0, w31
    bn.wsrr   w8, URND

    /* Load point P
       ([w11,w10], [w9,w8], [w7, w6]) <= P */
    li        x2, 6
    bn.lid    x2++, 0(x30)
    bn.lid    x2++, 32(x30)
    bn.lid    x2++, 64(x30)
    bn.lid    x2++, 96(x30)
    bn.lid    x2++, 128(x30)
    bn.lid    x2,   160(x30)

    /* Load point 2P
       ([w30,w29], [w28,w27], [w26, w25]) <= 2P */
    li        x2, 25
    bn.lid    x2++, 288(x30)
    bn.lid    x2++, 320(x30)
    bn.lid    x2++, 352(x30)
    bn.lid    x2++, 384(x30)
    bn.lid    x2++, 416(x30)
    bn.lid    x2,   448(x30)

    /* Select whether P or 2P will be stored in dmem[p_temp1].
       ([w21,w20], [w19,w18], [w17, w16]) <= M ? 2P : P */
    bn.sel    w16, w25, w6, M
    bn.sel    w17, w26, w7, M
    bn.sel    w18, w27, w8, M
    bn.sel    w19, w28, w9, M
    bn.sel    w20, w29, w10, M
    bn.sel    w21, w30, w11, M

    /* Store point 2P or P based on M
       dmem[p_temp1] <= ([w21,w20], [w19,w18], [w17, w16]) <= 2P or P */
    li        x2, 16
    bn.sid    x2++, 0(x7)
    bn.sid    x2++, 32(x7)
    bn.sid    x2++, 64(x7)
    bn.sid    x2++, 96(x7)
    bn.sid    x2++, 128(x7)
    bn.sid    x2,   160(x7)

    /* Randomize registers before using them again. */
    bn.wsrr   w16, URND
    bn.wsrr   w17, URND
    bn.wsrr   w18, URND
    bn.wsrr   w19, URND
    bn.wsrr   w20, URND
    bn.wsrr   w21, URND

    /* Select whether P or 2P will be stored in dmem[p_temp2].
       ([w21,w20], [w19,w18], [w17, w16]) <= M ? P : 2P */
    bn.sel    w16, w6,  w25, M
    bn.sel    w17, w7,  w26, M
    bn.sel    w18, w8,  w27, M
    bn.sel    w19, w9,  w28, M
    bn.sel    w20, w10, w29, M
    bn.sel    w21, w11, w30, M

    /* Store point P or 2P based on M
       dmem[p_temp2] <= ([w21,w20], [w19,w18], [w17, w16]) <= P or 2P */
    li        x2, 16
    bn.sid    x2++, 0(x8)
    bn.sid    x2++, 32(x8)
    bn.sid    x2++, 64(x8)
    bn.sid    x2++, 96(x8)
    bn.sid    x2++, 128(x8)
    bn.sid    x2,   160(x8)

    /* Load the MSB of d1.
       M <= MSB(d1) */
    li        x2, 1
    bn.lid    x2, 544(x30)
    bn.or     w8, w1, w31

    /* Select whether p_temp1 or p_temp2 will be stored in x27.
       x27 <= M ? p_temp1 : p_temp2 */
    csrrs     x3, FG0, x0
    andi      x3, x3, 2
    srli      x3, x3, 1
    sub       x2, x0, x3
    xor       x27, x7, x8
    and       x27, x27, x2
    xor       x27, x27, x8

    /* Reload randomized projective coodinates for curve point P.
       P = (x_p, y_p, z_p) = dmem[dptr_sp] <= (x*z mod p, y*z mod p, z) */
    jal       x1, store_proj_randomize

    /* Add points Q+P or Q+2P depending on offset in x27.
       Q_a = ([w30,w29], [w28,w27], [w26, w25]) <= Q + dmem[x27] */
    jal       x1, proj_add_p384

    /* load shares from scratchpad
       [w2, w1, w0] = s0; [w5, w4, w3] = s1 */
    li        x2, 0
    bn.lid    x2++, 192(x30)
    bn.lid    x2++, 224(x30)
    bn.lid    x2++, 256(x30)
    bn.lid    x2++, 480(x30)
    bn.lid    x2++, 512(x30)
    bn.lid    x2,   544(x30)

    /* M = s0[511] */
    bn.or     w8, w2, w31

    /* load q from scratchpad
        Q = ([w11,w10], [w9,w8], [w7,w6]) <= dmem[x26] */
    li        x2, 6
    bn.lid    x2++, 0(x26)
    bn.lid    x2++, 32(x26)
    bn.lid    x2++, 64(x26)
    bn.lid    x2++, 96(x26)
    bn.lid    x2++, 128(x26)
    bn.lid    x2,   160(x26)

    /* select either Q or Q_a
       if M: Q_temp = ([w21,w20], [w19,w18], [w17,w16]) <= Q_a else: Q_temp <= Q */
    bn.sel    w16, w25, w6, M
    bn.sel    w17, w26, w7, M
    bn.sel    w18, w27, w8, M
    bn.sel    w19, w28, w9, M
    bn.sel    w20, w29, w10, M
    bn.sel    w21, w30, w11, M

    /* Randomize registers before using them again. */
    bn.wsrr   w6, URND
    bn.wsrr   w7, URND
    bn.wsrr   w8, URND
    bn.wsrr   w9, URND
    bn.wsrr   w10, URND
    bn.wsrr   w11, URND

    /* M = s1[511] */
    bn.or     w8, w5, w31

    /* select either Q_temp or Q_a
       if M: Q = ([w21,w20], [w19,w18], [w17,w16]) <= Q_a else: Q <= Q_temp */
    bn.sel    w6, w25, w16, M
    bn.sel    w7, w26, w17, M
    bn.sel    w8, w27, w18, M
    bn.sel    w9, w28, w19, M
    bn.sel    w10, w29, w20, M
    bn.sel    w11, w30, w21, M

    /* store Q in dmem
     dmem[x26] = dmem[dptr_sc+512] <= [w21:w16] */
    li        x2, 6
    bn.sid    x2++, 0(x26)
    bn.sid    x2++, 32(x26)
    bn.sid    x2++, 64(x26)
    bn.sid    x2++, 96(x26)
    bn.sid    x2++, 128(x26)
    bn.sid    x2,   160(x26)

    /* left shift both shares
       s0 <= s0 << 1 ; s1 <= s1 << 1 */
    bn.wsrr   w10, URND
    bn.rshi   w5, w5, w4 >> 255
    bn.rshi   w4, w4, w3 >> 255
    bn.rshi   w3, w3, w10 >> 255
    bn.rshi   w10, w10, w31 >> 1
    bn.rshi   w2, w2, w1 >> 255
    bn.rshi   w1, w1, w0 >> 255
    bn.rshi   w0, w0, w10 >> 255

    /* store both shares in scratchpad */
    li        x2, 0
    bn.sid    x2++, 192(x30)
    bn.sid    x2++, 224(x30)
    bn.sid    x2++, 256(x30)
    bn.sid    x2++, 480(x30)
    bn.sid    x2++, 512(x30)
    bn.sid    x2,   544(x30)

    /* Get a fresh random number from URND and scale the coordinates of 2P.
       (scaling each proj. coordinate by same factor results in same point) */

    /* get a 384-bit random number from URND */
    bn.wsrr   w0, URND
    bn.wsrr   w1, URND
    bn.rshi   w1, w31, w1 >> 128

    /* reduce random number
      [w3, w2] = z <= [w1, w0] mod p */
    bn.sub    w10, w0, w12
    bn.subb   w11, w1, w13
    bn.sel    w2, w0, w10, C
    bn.sel    w3, w1, w11, C

    /* scale all coordinates in scratchpad */
    li        x2, 16
    li        x3, 17
    /* x-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 288(x30)
    bn.lid    x3, 320(x30)
    jal       x1, p384_mulmod_p
    bn.sid    x2, 288(x30)
    bn.sid    x3, 320(x30)
    /* y-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 352(x30)
    bn.lid    x3, 384(x30)
    jal       x1, p384_mulmod_p
    bn.sid    x2, 352(x30)
    bn.sid    x3, 384(x30)
    /* z-coordinate */
    bn.mov    w10, w2
    bn.mov    w11, w3
    bn.lid    x2, 416(x30)
    bn.lid    x3, 448(x30)
    jal       x1, p384_mulmod_p
    bn.sid    x2, 416(x30)
    bn.sid    x3, 448(x30)

  /* Load result Q into ([w21,w20], [w19,w18], [w17,w16]) <= Q */
  li        x2, 25
  bn.lid    x2++, 0(x26)
  bn.lid    x2++, 32(x26)
  bn.lid    x2++, 64(x26)
  bn.lid    x2++, 96(x26)
  bn.lid    x2++, 128(x26)
  bn.lid    x2,   160(x26)

  ret

/**
 * Routine to reblind a masked scalar.
 *
 * Adds a multiple of the curve order n to both shares of the
 * secret scalar d.
 *
 * For each share s a 194 bit random number r is generated and added
 * to the s as follows:
 *
 * s = (s + r * n) mod (n << 194)
 *
 * We have 194 bits of blinding for each share.
 * This is the minimal number of bits needed to protect against window
 * attacks mentioned in Schindler.
 * https://csrc.nist.gov/csrc/media/events/workshop-on-elliptic-curve-cryptography-standards/documents/papers/session6-schindler-werner.pdf
 *
 * @param[in]       [w11, w10]: n, domain parameter of P-384 curve
 *                              (order of base point G)
 * @param[in]              w31: all-zero
 * @param[in,out]  [w2, w1, w0]: first share of scalar d (578 bits)
 * @param[in,out]  [w5, w4, w3]: second share of scalar d (578 bits)
 *
 * clobbered registers: x10-x11, w0-w5, w19-w23
 * clobbered flag groups: FG0
 */
 .globl p384_masked_scalar_reblind
p384_masked_scalar_reblind:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* reblind first share of scalar d in [w1, w0]. */
  bn.mov    w16, w0
  bn.mov    w17, w1
  bn.mov    w18, w2
  jal       x1, p384_scalar_reblind
  bn.mov    w0, w16
  bn.mov    w1, w17
  bn.mov    w2, w18

  /* Randomize w16, w17 and w18 which contain the first share of scalar d. */
  bn.wsrr   w16, URND
  bn.wsrr   w17, URND
  bn.wsrr   w18, URND

  /* reblind second share of scalar d in [w3, w2]. */
  bn.mov    w16, w3
  bn.mov    w17, w4
  bn.mov    w18, w5
  jal       x1, p384_scalar_reblind
  bn.mov    w3, w16
  bn.mov    w4, w17
  bn.mov    w5, w18

  /* Randomize w16, w17 and w18 which contain the second share of scalar d. */
  bn.wsrr   w16, URND
  bn.wsrr   w17, URND
  bn.wsrr   w18, URND

  ret

/**
 * Helper routine to reblind a scalar.
 *
 * Adds a multiple of the curve order n to the secret scalar d.
 *
 * A 194 bit random number r is generated and added
 * to d as follows:
 *
 * d = (d + r * n) mod (n << 194)
 *
 * We have 194 bits of blinding for each share.
 * This is the minimal number of bits needed to protect against window
 * attacks mentioned in Schindler.
 * https://csrc.nist.gov/csrc/media/events/workshop-on-elliptic-curve-cryptography-standards/documents/papers/session6-schindler-werner.pdf
 *
 * @param[in]       [w11, w10]: n, domain parameter of P-384 curve
 *                              (order of base point G)
 * @param[in]  [w18, w17, w16]: scalar d (578 bits)
 * @param[in]              w31: all-zero
 * @param[out] [w18, w17, w16]: hidden scalar d (578 bits)
 *
 * clobbered registers: x10-x11, w19-w24
 * clobbered flag groups: FG0
 */
p384_scalar_reblind:

  /* Zero out multiplication registers. */
  bn.xor w22, w22, w22
  bn.xor w23, w23, w23
  bn.xor w24, w24, w24

  /* Get a fresh 194-bit random value r from URND.
       w20 = URND() */
  bn.wsrr   w20, URND
  bn.rshi   w20, w31, w20 >> 62

  /* [w24,w23,w22] <= m = r * n */
  bn.mulqacc.z          w20.0, w10.0,  0
  bn.mulqacc            w20.1, w10.0, 64
  bn.mulqacc.so  w22.L, w20.0, w10.1, 64
  bn.mulqacc            w20.2, w10.0,  0
  bn.mulqacc            w20.1, w10.1,  0
  bn.mulqacc            w20.0, w10.2,  0
  bn.mulqacc            w20.3, w10.0, 64
  bn.mulqacc            w20.2, w10.1, 64
  bn.mulqacc            w20.1, w10.2, 64
  bn.mulqacc.so  w22.U, w20.0, w10.3, 64
  bn.mulqacc            w20.3, w10.1,  0
  bn.mulqacc            w20.2, w10.2,  0
  bn.mulqacc            w20.1, w10.3,  0
  bn.mulqacc            w20.0, w11.0,  0
  bn.mulqacc            w20.3, w10.2, 64
  bn.mulqacc            w20.2, w10.3, 64
  bn.mulqacc            w20.1, w11.0, 64
  bn.mulqacc.so  w23.L, w20.0, w11.1, 64
  bn.mulqacc            w20.3, w10.3,  0
  bn.mulqacc            w20.2, w11.0,  0
  bn.mulqacc            w20.1, w11.1,  0
  bn.mulqacc            w20.3, w11.0, 64
  bn.mulqacc.so  w23.U, w20.2, w11.1, 64
  bn.mulqacc.so  w24.L, w20.3, w11.1,  0

  /* [w22,w21,w20] <= d + m */
  bn.add    w20, w16, w22
  bn.addc   w21, w17, w23
  bn.addc   w22, w18, w24
  bn.sub    w31, w31, w31  /* dummy instruction to clear flags */

  /* [w25,w24,w23] <= n << 194 */
  bn.rshi   w23, w10, w31 >> 62
  bn.rshi   w24, w11, w10 >> 62
  bn.rshi   w25, w31, w11 >> 62

  /* Reduce d + m modulo (n << 194) with a conditional subtraction.
       [w25,w24,w23] <= d + m mod (n << 194) */
  bn.sub    w23, w20, w23
  bn.subb   w24, w21, w24
  bn.subb   w25, w22, w25
  bn.sel    w16, w20, w23, FG0.C
  bn.sel    w17, w21, w24, FG0.C
  bn.sel    w18, w22, w25, FG0.C
  bn.sub    w31, w31, w31  /* dummy instruction to clear flags */

  ret
