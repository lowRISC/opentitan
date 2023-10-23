/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for ECDSA signature verification and curve point
 *   test.
 */

 .section .text

/**
 * 384-bit variable time modular multiplicative inverse computation
 *
 * Returns c <= a^(-1) mod m
 *         where 'a' is a bigint of length 384 bit with a < m
 *               'm' is the modulus with a length of 384 bit
 *               'c' is a 384-bit result
 *
 * This routine implements the computation of the modular multiplicative
 * inverse based on the binary GCD or Stein's algorithm.
 * The implemented variant is based on the "right-shift binary extended GCD"
 * as it is described in section 3.1 of [1] (Algorithm 1).
 * [1] https://doi.org/10.1155/ES/2006/32192
 *
 * Note that this is a variable time implementation. I.e. this routine will
 * show a data-dependent timing and execution profile. Only use where a
 * full white-box scenario is acceptable.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w30, w29]: a, 384-bit operand
 * @param[in]  [w13, w12]: m, modulus
 * @param[in]  w31: all-zero
 * @param[out] [w17,w16]: result c
 *
 * clobbered registers: x2, w2, w4 to w11, w16 to w19
 * clobbered flag groups: FG0
 */
mod_inv_var:
  /* [w5,w4] = r <= 0 */
  bn.xor    w4, w4, w4
  bn.xor    w5, w5, w5

  /* [w7,w6] = s <= 1 */
  bn.addi   w6, w31, 1
  bn.xor    w7, w7, w7

  /* [w9,w8] = u <= m = [w13, w12]*/
  bn.mov    w8, w12
  bn.mov    w9, w13

  /* [w11,w10] = v <= [w30, w29] */
  bn.mov    w10, w29
  bn.mov    w11, w30

  ebgcd_loop:
  /* test if u is odd */
  bn.or     w8, w8, w8
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 4
  bne       x2, x0, ebgcd_u_odd

  /* u is even: */
  /* [w9,w8] = u <= u/2 = [w9,w8] >> 1 */
  bn.rshi   w8, w9, w8 >> 1
  bn.rshi   w9, w31, w9 >> 1

  /* test if r is odd */
  bn.or     w4, w4, w4
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 4
  bne       x2, x0, ebgcd_r_odd

  /* r is even: */
  /* [w5,w4] = r <= r/2 = [w5,w4] >> 1 */
  bn.rshi   w4, w5, w4 >> 1
  bn.rshi   w5, w31, w5 >> 1
  jal       x0, ebgcd_loop

  ebgcd_r_odd:
  /* [w5,w4] = r <= (r + m)/2 = ([w5,w4] + [w13,w12]) >> 1 */
  bn.add    w4, w4, w12
  bn.addc   w5, w5, w13
  bn.rshi   w4, w5, w4 >> 1
  bn.rshi   w5, w31, w5 >> 1
  jal       x0, ebgcd_loop

  ebgcd_u_odd:
  /* test if v is odd */
  bn.or     w10, w10, w10
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 4
  bne       x2, x0, ebgcd_uv_odd

  /* v is even: */
  /* [w11,w10] = v <= v/2 = [w11,w10] >> 1 */
  bn.rshi   w10, w11, w10 >> 1
  bn.rshi   w11, w31, w11 >> 1

  /* test if s is odd */
  bn.or     w6, w6, w6
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 4
  bne       x2, x0, ebgcd_s_odd

  /* s is even: */
  /* [w7,w6] = s <= s/2 = [w7,w6] >> 1 */
  bn.rshi   w6, w7, w6 >> 1
  bn.rshi   w7, w31, w7 >> 1
  jal       x0, ebgcd_loop

  ebgcd_s_odd:
  /* [w7,w6] = s <= (s + m)/2 = ([w7,w6] + [w13,w12]) >> 1 */
  bn.add    w6, w6, w12
  bn.addc   w7, w7, w13
  bn.rshi   w6, w7, w6 >> 1
  bn.rshi   w7, w31, w7 >> 1
  jal       x0, ebgcd_loop

  ebgcd_uv_odd:
  /* test if v >= u */
  bn.cmp    w10, w8
  bn.cmpb   w11, w9
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  beq       x2, x0, ebgcd_v_gte_u

  /* u > v: */
  /* [w5,w4] = r <= r - s = [w5,w4] - [w7,w6]; if (r < 0): r <= r + m */
  bn.sub    w4, w4, w6
  bn.subb   w5, w5, w7
  bn.add    w18, w4, w12
  bn.addc   w19, w5, w13
  bn.sel    w4, w18, w4, C
  bn.sel    w5, w19, w5, C

  /* [w9,w8] = u <= u - v = [w9,w8] - [w11,w10] */
  bn.sub    w8, w8, w10
  bn.subb   w9, w9, w11
  jal       x0, ebgcd_loop

  ebgcd_v_gte_u:
  /* [w7,w6] = s <= s - r = [w7,w6] - [w5,w4]; if (s < 0) s <= s + m */
  bn.sub    w6, w6, w4
  bn.subb   w7, w7, w5
  bn.add    w18, w6, w12
  bn.addc   w19, w7, w13
  bn.sel    w6, w18, w6, C
  bn.sel    w7, w19, w7, C

  /* [w11,w10] = v <= v - u = [w11,w10] - [w9,w8] */
  bn.sub    w10, w10, w8
  bn.subb   w11, w11, w9

  /* if v > 0 go back to start of loop */
  bn.cmp    w31, w10
  bn.cmpb   w31, w11
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  bne       x2, x0, ebgcd_loop

  /* v <= 0: */
  /* if (r > m): [w17,w16] = a <= r - m = [w5,w4] - [w13,w12]
     else: [w17,w16] = a <= r = [w5,w4] */
  bn.sub    w18, w4, w12
  bn.subb   w19, w5, w13
  bn.cmp    w12, w4
  bn.cmpb   w13, w5
  bn.sel    w16, w18, w4, C
  bn.sel    w17, w19, w5, C

  ret


/**
 * Store curve point in projective coordinates (non randomized)
 *
 * Reads an affine P-384 from dmem, addressed by two independent pointers for
 * the affine x- and y-coordinate respectively and stores the same point in
 * projective form at another dmem location. The destination address is given
 * by a single pointer. All 3 coordinates (x,y,z) are consecutively stored in
 * this order in little endian format, 256 bit aligned.
 *
 * This routine does not randomize the point, hence the z-cooridnate is simply
 * set to 1.
 *
 * @param[in]  x10: dptr_x_a, pointer to affine x-coordinate of curve point
 * @param[in]  x11: dptr_y_a, pointer to affine y-coordinate of curve point
 * @param[in]  x12: dptr_proj, pointer to destination address
 * @param[in]  w31: all-zero
 * @param[out] x12: next dmem address after stored point (256-bit aligned)
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2, x12, w6 to w11
 * clobbered flag groups: FG0
 */
store_aff_proj:

  /* load point */
  li        x2, 6
  bn.lid    x2++, 0(x10)
  bn.lid    x2++, 32(x10)
  bn.lid    x2++, 0(x11)
  bn.lid    x2++, 32(x11)
  bn.addi   w10, w31, 1
  bn.xor    w11, w11, w11

  /* store point */
  li        x2, 6
  loopi 6, 2
    bn.sid    x2, 0(x12++)
    addi      x2, x2, 1
  nop

  ret


/**
 * Store curve point in projective coordinates (non randomized)
 *
 * Stores a P-384 curve point located in 6 consecutive WDRs at a dmem location
 * given by a pointer. All 3 coordinates (x,y,z) are consecutively stored in
 * this order in little endian format, 256 bit aligned.
 *
 * This routine does not randomize the point.
 *
 * @param[in]  x12: dptr_proj, pointer to destination address
 * @param[in]  [w26,w25]: x-coordinate of curve point
 * @param[in]  [w28,w27]: y-coordinate of curve point
 * @param[in]  [w30,w29]: z-coordinate of curve point
 * @param[out] x12: next dmem address after stored point (256-bit aligned)
 *
 * Flags: This routine doe not set any flags.
 *
 * clobbered registers: x2, x12
 * clobbered flag groups: none
 */
store_proj:
  li        x2, 25
  loopi 6, 2
    bn.sid    x2, 0(x12++)
    addi      x2, x2, 1
  nop
  ret

/**
 * P-384 ECDSA signature verification
 *
 * returns the affine x-coordinate of
 *         (x1, y1) = u1*G + u2*Q
 *         with u1 = z*s^-1 mod n  and  u2 = r*s^-1 mod n
 *         where G is the curve's base point,
 *               z is the message
 *               r, s is the signature
 *               Q is the public key.
 *
 * The routine computes the x1 coordinate and places it in dmem. x1 will be
 * reduced (mod n), however, the final comparison has to be performed on the
 * host side. The signature is valid if x1 == r.
 * This routine runs in variable time.
 *
 * @param[in]  dmem[4]: dptr_rnd, pointer to dmem location where the reduced
 *                           affine x1-coordinate will be stored
 * @param[in]  dmem[8]: dptr_msg, pointer to the message to be verified in dmem
 * @param[in]  dmem[12]: dptr_r, pointer to r of signature in dmem
 * @param[in]  dmem[16]: dptr_s, pointer to s of signature in dmem
 * @param[in]  dmem[20]: dptr_x, pointer to x-coordinate of public key in dmem
 * @param[in]  dmem[20]: dptr_y, pointer to y-coordinate of public key in dmem
 *
 * Scratchpad memory layout:
 * The routine expects at least 896 bytes of scratchpad memory at dmem
 * location 'scratchpad' (sp). Internally the scratchpad is used as follows:
 * dptr_sp     .. dptr_sp+191: point C, projective
 * dptr_sp+192 .. dptr_sp+383: point G, projective
 * dptr_sp+384 .. dptr_sp+575: point Q, projective
 * dptr_sp+576 .. dptr_sp+767: point Q+G, projective
 * dptr_sp+768 .. dptr_sp+831: scalar u1
 * dptr_sp+832 .. dptr_sp+896: scalar u2
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2 to x5, x10, x11, x12, x22 to 28, w0 to w31
 * clobbered flag groups: FG0
 */
.globl p384_verify
p384_verify:

  /* init all-zero reg */
  bn.xor    w31, w31, w31

  /* load domain parameter n (order of base point)
     [w13, w12] <= n = dmem[p384_n] */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load s of signature from dmem
     [w30,w29] <= s = dmem[*dptr_s] */
  li        x2, 29
  la        x3, dptr_s
  lw        x3, 0(x3)
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* goto 'fail' if [w30,w29] == [w31, w31] <=> s == 0 */
  bn.cmp    w31, w29
  bn.cmpb   w31, w30
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  beq       x2, x0, fail

  /* goto 'fail' if [w30,w29] >= [w12,w13] <=> s >= n */
  bn.cmp    w29, w12
  bn.cmpb   w30, w13
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  beq       x2, x0, fail

  /* Compute modular inverse of S
     Note: This can be replaced by the 'mod_inv_n_p384' subroutine at the
           cost of ~60k cycles if reduced code size is targeted */
  /* [w9,w8] <= [w17,w16] <= s^-1  mod n = [w30,w29]^-1 mod [w13,w12] */
  jal       x1, mod_inv_var
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* Compute Solinas constant k for modulus n (we know it is only 191 bits, so
     no need to compute the high part):
     w14 <= 2^256 - n[255:0] = (2^384 - n) mod (2^256) = 2^384 - n */
  bn.sub    w14, w31, w12

  /* set regfile pointers to in/out regs of Barrett routine */
  li        x22, 10
  li        x23, 11
  li        x24, 16
  li        x25, 17

  /* load r of signature from dmem
     [w11,w10] <= r = dmem[*dptr_r] */
  li        x2, 10
  la        x3, dptr_r
  lw        x3, 0(x3)
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* goto 'fail' if [w11, w10] == [w31, w31] <=> r == 0 */
  bn.cmp    w31, w10
  bn.cmpb   w31, w11
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  beq       x2, x0, fail

  /* goto 'fail' if [w11,w10] >= [w12,w13] <=> r >= n */
  bn.cmp    w10, w12
  bn.cmpb   w11, w13
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1
  beq       x2, x0, fail

  /* u2 = [w3,w2] <= [w17,w16] <= r*s^-1 mod n
        = [w11,w10]*[w17,w16] mod [w13,w12] */
  jal x1, p384_mulmod_n
  bn.mov    w2, w16
  bn.mov    w3, w17
  /* left align */
  bn.rshi   w3, w3, w2 >> 128
  bn.rshi   w2, w2, w31 >> 128

  /* load message from dmem
     [w11,w10] <= msg = dmem[*dptr_msg] */
  li        x2, 10
  la        x3, dptr_msg
  lw        x3, 0(x3)
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* u1 = [w1,w0] <= [w17,w16] <= msg*s^-1 mod n
        = [w11,w10]*[w9,w8] mod [w13,w12] */
  bn.mov    w16, w8
  bn.mov    w17, w9
  jal       x1, p384_mulmod_n
  bn.mov    w0, w16
  bn.mov    w1, w17
  /* left align */
  bn.rshi   w1, w1, w0 >> 128
  bn.rshi   w0, w0, w31 >> 128

  /* store u1 and u2 in scratchpad
     scratchpad[768] <= u1; scratchpad[832] <= u2 */
  li        x2, 0
  la        x26, scratchpad
  bn.sid    x2++, 768(x26)
  bn.sid    x2++, 800(x26)
  bn.sid    x2++, 832(x26)
  bn.sid    x2++, 864(x26)

  /* load domain parameter p (modulus)
     [w13, w12] <= p = dmem[p384_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* set dmem pointer to domain parameter b */
  la        x28, p384_b

  /* init double and add algorithm with C = (0, 1, 0)
     GQ = (x,y,z) = scratchpad[0] <= (0, 1, 0) */
  bn.xor    w25, w25, w25
  bn.xor    w26, w26, w26
  bn.addi   w27, w31, 1
  bn.xor    w28, w28, w28
  bn.xor    w29, w29, w29
  bn.xor    w30, w30, w30
  la        x12, scratchpad
  jal       x1, store_proj

  /* load base point G and use in projective form (set z to 1)
     G = (x,y,z) = scratchpad[192] <= (dmem[p384_gy], dmem[p384_gy], 1) */
  la        x10, p384_gx
  la        x11, p384_gy
  jal       x1, store_aff_proj

  /* load public key Q from dmem and use in projective form (set z to 1)
     Q = (x,y,z) = scratchpad[384] <= (dmem[*dptr_x], dmem[*dptr_y], 1) */
  la        x3, dptr_x
  lw        x10, 0(x3)
  la        x3, dptr_y
  lw        x11, 0(x3)
  jal       x1,  store_aff_proj

  /* The remaining part of the routine implements a variable time
     double-and-add algorithm. For the signature verification we need to
     compute the point C = (x1, y1) = u1*G + _2*Q. This can be done in a
     single double-and-add routine by using Shamir's Trick. */

  /* Compute G+Q and store in dmem
     GQ = (x,y,z) = dmem[dptr_sp+576]
        <= sp[dptr_sp+192] (+) dmem[dptr_sp+384] */
  la        x26, scratchpad
  addi      x27, x26, 384
  addi      x26, x26, 192
  jal       x1, proj_add_p384
  jal       x1, store_proj

  la        x26, scratchpad

  /* main loop with decreasing index i (i=383 downto 0) */
  loopi     384, 35

    /* probe MSBs of u1 and u2 and u1|u2 to determine which point has to be
       added. */

    /* load u1 and u2 from scratchpad
       [w1,w0] <= u1; [w3, w2] = u2 */
    li        x2, 0
    bn.lid    x2++, 768(x26)
    bn.lid    x2++, 800(x26)
    bn.lid    x2++, 832(x26)
    bn.lid    x2++, 864(x26)

    /* left shift u1 = [w1,w0] <= [w1,w0] << 1 */
    bn.add    w0, w0, w0
    bn.addc   w1, w1, w1

    /* keep MSB/carry bit in x3: x3 <= u1[i] */
    csrrs     x3, 0x7c0, x0
    andi      x3, x3, 1

    /* left shift u2 = [w3,w2] <= [w3,w2] << 1 */
    bn.add    w2, w2, w2
    bn.addc   w3, w3, w3

    /* keep MSB/carry bit in x3: x4 <= u2[i] */
    csrrs     x4, 0x7c0, x0
    andi      x4, x4, 1
    li        x2, 0

    /* write back u1 and u2 to scratchpad */
    bn.sid    x2++, 768(x26)
    bn.sid    x2++, 800(x26)
    bn.sid    x2++, 832(x26)
    bn.sid    x2++, 864(x26)

    /* test if at least one MSb of the scalars is 1
       x5 <= x4 | x3 = u1[i] | u2[i] */
    or        x5, x4, x3

    /* always double, let both input pointers for point addition point to C */
    add       x27, x26, x0

    /* no addition if x5 = u1[i] | u2[i] == 0 */
    beq       x5, x0, ver_end_loop

    /* perform point doubling C <= 2 (*) C */
    jal       x1, proj_add_p384
    addi      x12, x26, 0
    jal       x1, store_proj

    /* check if u1[i] is set */
    bne       x3, x0, u1_set

    /* only u2[i] is set: do C <= C + Q */
    addi      x27, x26, 384
    jal       x0, ver_end_loop

    u1_set:
    /* chek if u2[i] is set as well */
    bne       x4, x0, both

    /* only u1[i] is set: do C <= C + G */
    add       x27, x26, 192
    jal       x0, ver_end_loop

    /* both bits at current index (u1[i] and u2[i]) are set:
       do: C <= C + (G + Q) */
    both:
    addi      x27, x26, 576

    ver_end_loop:
    /* perform addition of selected point here, or point doubling in case
       of no addition */
    jal       x1, proj_add_p384
    addi      x12, x26, 0
    jal       x1, store_proj
    nop

  /* compute inverse of z-coordinate: [w1,w0] <= z_c^-1  mod p */
  jal       x1, mod_inv_var

  /* convert x-coordinate of C back to affine: x1 = x_c * z_c^-1  mod p */
  bn.mov    w10, w25
  bn.mov    w11, w26
  jal x1, p384_mulmod_p

  /* load domain parameter n (order of base point)
     [w13, w12] <= n = dmem[p384_n] */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* final reduction: [w5,w4] = x1 <= x1 mod n = [w17,w16] mod [w13,w12] */
  bn.sub    w4, w16, w12
  bn.subb   w5, w17, w13
  bn.sel    w4, w16, w4, C
  bn.sel    w5, w17, w5, C

  fail:

  /* store affine x-coordinate in dmem: dmem[dptr_rnd] <= x1 = [w5,w4] */
  li        x2, 4
  la        x3, dptr_rnd
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

/* pointer to rnd (dptr_rnd)
   used for result here */
.globl dptr_rnd
dptr_rnd:
  .zero 4

/* pointer to msg (dptr_msg) */
.globl dptr_msg
dptr_msg:
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

/* Scratchpad memory */
.balign 32
scratchpad:
  .zero 896
