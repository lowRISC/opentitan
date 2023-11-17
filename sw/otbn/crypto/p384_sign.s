/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for ECDSA signature generation.
 */

 .section .text

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
 * @param[in]  dmem[0]: dptr_k0, pointer to location in dmem containing
 *                      1st scalar share k0
 * @param[in]  dmem[4]: dptr_k1, pointer to location in dmem containing
 *                      2nd scalar share k1
 * @param[in]  dmem[8]: dptr_msg, pointer to the message to be signed in dmem
 * @param[in]  dmem[12]: dptr_r, pointer to dmem location where s component
 *                               of signature will be placed
 * @param[in]  dmem[16]: dptr_s, pointer to dmem location where r component
 *                               of signature will be placed
 * @param[in]  dmem[28]: dptr_d0, pointer to location in dmem containing
 *                      1st private key share d0
 * @param[in]  dmem[32]: dptr_d1, pointer to location in dmem containing
 *                      2nd private key share d1
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2 to x6, x9 to x15, x17 to x28, x30
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

  /* set dmem pointer to 1st scalar share k0 */
  la        x17, dptr_k0
  lw        x17, 0(x17)

  /* set dmem pointer to 2nd scalar share k1 */
  la        x19, dptr_k1
  lw        x19, 0(x19)

  /* set dmem pointer to 1st private key share d0 */
  la        x4, dptr_d0
  lw        x4, 0(x4)

  /* set dmem pointer to 2nd private key share d1 */
  la        x5, dptr_d1
  lw        x5, 0(x5)

  /* set dmem pointer to message msg */
  la        x6, dptr_msg
  lw        x6, 0(x6)

  /* set dmem pointer to signature r */
  la        x14, dptr_r
  lw        x14, 0(x14)

  /* set dmem pointer to signature s */
  la        x15, dptr_s
  lw        x15, 0(x15)

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

  /* scalar multiplication with base point and
     conversion of projective coordinates to affine space
     [w28:w25] <= (x_1, y_1) = (k*alpha) * G */
  jal       x1, scalar_mult_int_p384
  jal       x1, proj_to_affine_p384

  /* store r of signature in dmem: dmem[dptr_r] <= r = [w26,w25] */
  li        x2, 25
  bn.sid    x2++, 0(x14)
  bn.sid    x2++, 32(x14)

  /* load domain parameter n (order of base point)
     [w13, w12] <= n = dmem[p384_n] */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Compute Solinas constant k for modulus n (we know it is only 191 bits, so
     no need to compute the high part):
     w14 <= 2^256 - n[255:0] = (2^384 - n) mod (2^256) = 2^384 - n */
  bn.sub    w14, w31, w12

  /* Multiplicative masking of shares k0 and k1 */

  /* Generate a random 127-bit number.
     w4 <= URND()[255:129] */
  bn.wsrr   w4, URND
  bn.rshi   w4, w31, w4 >> 129

  /* Add 1 to get a 128-bit nonzero scalar for masking.
     w4 <= w4 + 1 = alpha */
  bn.addi   w4, w4, 1

  /* load 1st share k0 from dmem
     [w11,w10] <= k0 = dmem[dptr_k0] */
  li        x2, 10
  bn.lid    x2++, 0(x17)
  bn.lid    x2++, 32(x17)

  /* [w26,w25] <= ([w11,w10] * w4) mod n = (k0 * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* load 2nd share k1 from dmem
     [w11,w10] <= k1 = dmem[dptr_k1] */
  li        x2, 10
  bn.lid    x2++, 0(x19)
  bn.lid    x2++, 32(x19)

  /* [w28,w27] <= ([w11,w10] * w4) mod n = (k1 * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* Multiplicative masking of shares d0 and d1 */

  /* load 1st share d0 from dmem
     [w11,w10] <= d0 = dmem[dptr_d0] */
  li        x2, 10
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* [w7,w6] <= ([w11,w10] * w4) mod n = (d0 * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* load 2nd share d1 from dmem
     [w11,w10] <= d1 = dmem[dptr_d1] */
  li        x2, 10
  bn.lid    x2++, 0(x5)
  bn.lid    x2++, 32(x5)

  /* [w9,w8] <= ([w11,w10] * w4) mod n = (d1 * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* Multiplicative masking of message msg */

  /* load message from dmem
     [w11, w10] <= msg = dmem[dptr_msg] */
  li        x2, 10
  bn.lid    x2++, 0(x6)
  bn.lid    x2++, 32(x6)

  /* [w1,w0] <= ([w11,w10] * w4) mod n = (msg * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* Compute (k*alpha) mod n = (k0*alpha + k1*alpha) mod n
     [w17,w16] <= k*alpha = [w26,w25] + [w28,w27] mod n */
  bn.add    w18, w27, w25
  bn.addc   w19, w28, w26
  bn.mov    w20, w31
  jal       x1, p384_reduce_n

  /* modular multiplicative inverse of k
     [w3, w2] <= [w17, w16] <= (k*alpha)^(-1) mod n */
  bn.mov    w29, w16
  bn.mov    w30, w17
  jal       x1, mod_inv_n_p384
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* Compute (d*alpha) mod n = (d0*alpha + d1*alpha) mod n
     [w17,w16] <= d*alpha = [w7,w6] + [w9,w8] mod n */
  bn.add    w18, w8, w6
  bn.addc   w19, w9, w7
  bn.mov    w20, w31
  jal       x1, p384_reduce_n

  /* [w17, w16] <= (k*alpha)^(-1)*d*alpha mod n = [w3, w2] * [w17, w16] mod [w13, w12] */
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, p384_mulmod_n

  /* load r of signature from dmem
     [w11,w10] <= r = dmem[dptr_r] */
  li        x2, 10
  bn.lid    x2++, 0(x14)
  bn.lid    x2++, 32(x14)

  /*  [w5, w4] <= [w17, w16]
        <= r * (k^(-1)*d) mod n = r * ((k*alpha)^(-1)*d*alpha) mod n =
           = [w11, w10] * [w17, w16] mod [w13, w12] */
  jal       x1, p384_mulmod_n
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* [w17, w16] <= k^(-1) * msg =
                   = (k*alpha)^(-1) * msg*alpha =
                   = [w3, w2]*[w1, w0] mod n */
  bn.mov    w10, w0
  bn.mov    w11, w1
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
  bn.sid    x2++, 0(x15)
  bn.sid    x2++, 32(x15)

  ret


/* pointers and scratchpad memory */
.section .data

.balign 32

/* pointer to k0 (dptr_k0) */
.globl dptr_k0
.weak dptr_k0
dptr_k0:
  .zero 4

/* pointer to k1 (dptr_k1) */
.globl dptr_k1
.weak dptr_k1
dptr_k1:
  .zero 4

/* pointer to msg (dptr_msg) */
.globl dptr_msg
.weak dptr_msg
dptr_msg:
  .zero 4

/* pointer to R (dptr_r) */
.globl dptr_r
.weak dptr_r
dptr_r:
  .zero 4

/* pointer to S (dptr_s) */
.globl dptr_s
.weak dptr_s
dptr_s:
  .zero 4

/* pointer to X (dptr_x) */
.globl dptr_x
.weak dptr_x
dptr_x:
  .zero 4

/* pointer to Y (dptr_y) */
.globl dptr_y
.weak dptr_y
dptr_y:
  .zero 4

/* pointer to d0 (dptr_d0) */
.globl dptr_d0
.weak dptr_d0
dptr_d0:
  .zero 4

/* pointer to d1 (dptr_d1) */
.globl dptr_d1
.weak dptr_d1
dptr_d1:
  .zero 4

/* 704 bytes of scratchpad memory */
.balign 32
.globl scratchpad
.weak scratchpad
scratchpad:
  .zero 704
